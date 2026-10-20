"""Independent checks of the predetermined practical batch schedule.

Run with this package's src directory on PYTHONPATH. These checks use actual
Born multinomial draws and independently reconstruct complete-record fits.
"""
import math
import unittest
from unittest.mock import patch

import numpy as np

from adaptive_tomography import estimators, mixed, pure, schedules


TARGETS = [256, 512] + list(range(1024, 16385, 1024))
EXPECTED_REPORTS = [256, 512, 1020, 2064, 3078, 4070, 5169, 6182,
                    7105, 8164, 9197, 10157, 11217, 12387, 13409,
                    14232, 15408, 16384]


def independent_sizes(maximum):
    """Literal real-arithmetic recurrence, independently of integer ceiling."""
    result = []
    total = 0
    while total < maximum:
        proposed = 16 if not result else max(16, math.ceil(total / 50))
        result.append(min(proposed, maximum - total))
        total += result[-1]
    return result


def projector(vector):
    return np.outer(vector, vector.conj())


class RecordedGenerator:
    def __init__(self, seed):
        self.rng = np.random.default_rng(seed)
        self.sizes = []
        self.probabilities = []
        self.counts = []

    def multinomial(self, size, probabilities):
        self.sizes.append(int(size))
        self.probabilities.append(probabilities.copy())
        counts = self.rng.multinomial(size, probabilities)
        self.counts.append(counts.copy())
        return counts


class PredeterminedScheduleTests(unittest.TestCase):
    def test_full_schedule_matches_independent_recurrence(self):
        actual = schedules.batch_sizes(16384)
        np.testing.assert_array_equal(actual, independent_sizes(16384))
        self.assertEqual(len(actual), 202)
        self.assertEqual(int(actual.sum()), 16384)
        np.testing.assert_array_equal(actual[:50], np.full(50, 16))
        self.assertEqual(actual[50], 16)
        self.assertEqual(actual[51], 17)

    def test_only_final_batch_can_be_clipped(self):
        for maximum in (16, 17, 1001, 16384):
            with self.subTest(maximum=maximum):
                sizes = schedules.batch_sizes(maximum)
                self.assertTrue(np.all(sizes > 0))
                total = 0
                for index, size in enumerate(sizes):
                    nominal = 16 if index == 0 else max(16, math.ceil(total / 50))
                    if index + 1 < len(sizes):
                        self.assertEqual(size, nominal)
                    else:
                        self.assertEqual(size, min(nominal, maximum - total))
                    total += int(size)
                self.assertEqual(total, maximum)
        sizes = schedules.batch_sizes(16384)
        self.assertEqual(sizes[-1], 31)
        self.assertEqual(math.ceil(int(sizes[:-1].sum()) / 50), 328)

    def test_published_reports_are_nearest_actual_endpoints(self):
        sizes = schedules.batch_sizes(16384)
        original = sizes.copy()
        endpoints = np.cumsum(sizes)
        independent = [min(endpoints, key=lambda n: (abs(int(n) - t), int(n)))
                       for t in TARGETS]
        actual = schedules.nearest_reporting_horizons(sizes, TARGETS)
        np.testing.assert_array_equal(actual, independent)
        np.testing.assert_array_equal(actual, EXPECTED_REPORTS)
        np.testing.assert_array_equal(sizes, original)
        self.assertTrue(np.all(np.isin(actual, endpoints)))
        self.assertNotIn(1024, endpoints)

    def test_nearest_ties_choose_earlier_completed_batch(self):
        actual = schedules.nearest_reporting_horizons(np.array([16, 16]), [24, 32])
        np.testing.assert_array_equal(actual, [16, 32])

    def test_unreachable_reports_are_rejected_without_splitting(self):
        sizes = schedules.batch_sizes(16384)
        for reports in ([1024, 16384], [256, 16383]):
            with self.subTest(reports=reports), self.assertRaises(ValueError):
                schedules.validated_batch_sizes(sizes, np.array(reports))
        validated = schedules.validated_batch_sizes(sizes, np.array(EXPECTED_REPORTS))
        np.testing.assert_array_equal(validated, sizes)

    def test_invalid_batch_vectors_are_rejected(self):
        for sizes in ([], [16, 0, 16], [16, -1, 17], [16., 16.], [8, 24]):
            with self.subTest(sizes=sizes), self.assertRaises(ValueError):
                schedules.validated_batch_sizes(sizes, np.array([32]))

    def test_optional_default_remains_doubling(self):
        horizons = np.array([2**12, 2**16, 2**20, 2**24])
        actual = schedules.validated_batch_sizes(None, horizons)
        expected = np.array([16] + [2**power for power in range(4, 24)])
        np.testing.assert_array_equal(actual, expected)
        self.assertEqual(len(actual), 21)
        self.assertEqual(int(actual.sum()), 2**24)
        self.assertTrue(np.all(np.isin(horizons, np.cumsum(actual))))


class GrowingBatchEstimatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sizes = schedules.batch_sizes(16384)
        cls.reports = np.asarray(EXPECTED_REPORTS)
        cls.mixed_truth = .9 * np.array([1., 2., 3.]) / np.sqrt(14)
        cls.reference, _, _ = pure.reference_measurement(4)
        cls.pure_truth = np.sqrt(np.arange(1, 5)) * np.exp(.37j * np.arange(4))
        cls.pure_truth /= np.linalg.norm(cls.pure_truth)

    def test_mixed_all_202_batches_enter_literal_scalar_ridge_fit(self):
        for rule in ("bures", "frobenius"):
            with self.subTest(rule=rule):
                rng = RecordedGenerator(77401)
                selected_axes = []
                original = mixed.measurement_design

                def record_design(*args):
                    axes, probabilities = original(*args)
                    selected_axes.append(axes.copy())
                    return axes, probabilities

                with patch.object(mixed, "measurement_design", side_effect=record_design):
                    _, rows = mixed.trajectory(rule, self.mixed_truth, rng,
                                               np.array([16384]), diagnostic=True,
                                               batch_sizes=self.sizes)
                self.assertEqual(rng.sizes, independent_sizes(16384))
                self.assertEqual(sum(map(np.sum, rng.counts)), 16384)
                matrix = np.eye(3)
                rhs = np.zeros(3)
                for axes, flat_counts in zip(selected_axes, rng.counts):
                    counts = flat_counts.reshape(3, 2)
                    for k in range(3):
                        for sign_index, sign in enumerate((-1, 1)):
                            multiplicity = int(counts[k, sign_index])
                            matrix += multiplicity * np.outer(axes[k], axes[k])
                            rhs += multiplicity * sign * axes[k]
                expected = np.linalg.solve(matrix, rhs)
                np.testing.assert_allclose(rows[-1]["raw_estimate"], expected,
                                           rtol=2e-13, atol=2e-13)

    def test_mixed_reports_do_not_change_the_measurement_record(self):
        for rule in ("bures", "frobenius"):
            with self.subTest(rule=rule):
                sparse_rng, dense_rng = RecordedGenerator(773), RecordedGenerator(773)
                sparse, _ = mixed.trajectory(rule, self.mixed_truth, sparse_rng,
                                             np.array([16384]), batch_sizes=self.sizes)
                dense, _ = mixed.trajectory(rule, self.mixed_truth, dense_rng,
                                            self.reports, batch_sizes=self.sizes)
                np.testing.assert_array_equal(sparse_rng.counts, dense_rng.counts)
                np.testing.assert_array_equal(sparse_rng.probabilities, dense_rng.probabilities)
                np.testing.assert_array_equal(sparse[-1], dense[-1])

    def test_pure_all_records_enter_ridge_and_tangent_correction(self):
        rng = RecordedGenerator(1899)
        original_correction = pure.correction
        captured = {}

        def inspect_correction(h, records, reference, ridge):
            captured["h"] = h.copy()
            captured["records"] = records
            corrected = original_correction(h, records, reference, ridge)
            captured["corrected"] = corrected.copy()
            return corrected

        with patch.object(pure, "correction", side_effect=inspect_correction):
            losses, _, _ = pure.trajectory(4, self.reference, self.pure_truth, rng,
                                           np.array([16384]), validate=True,
                                           batch_sizes=self.sizes)
        self.assertEqual(rng.sizes, independent_sizes(16384))
        records = captured["records"]
        self.assertEqual(len(records), 202)
        self.assertEqual([int(record.counts.sum()) for record in records], rng.sizes)
        self.assertEqual(sum(int(record.counts.sum()) for record in records), 16384)
        hb = estimators.hermitian_basis(4)
        matrix, rhs = np.eye(16), np.zeros(16)
        for record in records:
            features = np.asarray([[np.trace(effect @ basis).real for basis in hb]
                                   for effect in record.effects])
            matrix += int(record.counts.sum()) * (features.T @ features)
            rhs += features.T @ record.counts
        coefficients = np.linalg.solve(matrix, rhs)
        raw = sum(value * basis for value, basis in zip(coefficients, hb))
        _, eigenvectors = np.linalg.eigh(raw)
        np.testing.assert_allclose(projector(captured["h"]),
                                   projector(eigenvectors[:, -1]), atol=3e-12)
        literal = estimators.weighted_tangent_update(captured["h"], records,
                                                     self.reference, ridge=1.)
        self.assertEqual(literal["copies_used"], 16384)
        np.testing.assert_allclose(projector(captured["corrected"]),
                                   literal["state"], atol=3e-12)
        for method, vector in enumerate((captured["h"], captured["corrected"])):
            expected = pure.physical_losses(self.pure_truth, vector, 16384)
            np.testing.assert_allclose(losses[-1, method], expected, atol=1e-12)

    def test_pure_reports_do_not_change_the_measurement_record(self):
        sparse_rng, dense_rng = RecordedGenerator(988), RecordedGenerator(988)
        sparse, _, _ = pure.trajectory(4, self.reference, self.pure_truth, sparse_rng,
                                       np.array([16384]), batch_sizes=self.sizes)
        dense, _, _ = pure.trajectory(4, self.reference, self.pure_truth, dense_rng,
                                      self.reports, batch_sizes=self.sizes)
        np.testing.assert_array_equal(sparse_rng.counts, dense_rng.counts)
        np.testing.assert_allclose(sparse_rng.probabilities, dense_rng.probabilities,
                                   atol=2e-14, rtol=2e-13)
        np.testing.assert_allclose(sparse[-1], dense[-1], atol=2e-10, rtol=2e-12)

    def test_batch_sizes_are_independent_of_observed_counts(self):
        observed = []
        for seed in (23, 5981):
            rng = RecordedGenerator(seed)
            mixed.trajectory("frobenius", self.mixed_truth, rng,
                             np.array([16384]), batch_sizes=self.sizes)
            observed.append(rng.sizes)
        self.assertEqual(observed[0], observed[1])
        self.assertEqual(observed[0], independent_sizes(16384))


if __name__ == "__main__":
    unittest.main()
