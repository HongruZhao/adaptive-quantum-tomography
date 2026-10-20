"""Independent numerical checks of the paper's observation laws and objectives.

These tests expand small count records into individual observations and solve
the displayed objectives independently. They do not test an asymptotic theorem
by asking a finite Monte Carlo sample to equal its limiting constant.
"""
import unittest
from unittest.mock import patch

import numpy as np

from adaptive_tomography import estimators, mixed, optional, pure


def projector(h):
    return np.outer(h, h.conj())


def hermitian_square_root(a):
    values, vectors = np.linalg.eigh((a + a.conj().T) / 2)
    if values.min() < -1e-12:
        raise AssertionError("The test density matrix is not positive.")
    return (vectors * np.sqrt(np.maximum(values, 0))) @ vectors.conj().T


def independent_tangent_basis(h):
    """Use an eigenspace complement, independently of the production frame."""
    _, vectors = np.linalg.eigh(np.eye(len(h)) - projector(h))
    complement = vectors[:, 1:]
    tangents = []
    for phase in (1, 1j):
        for column in complement.T:
            v = phase * column / np.sqrt(2)
            tangents.append(np.outer(v, h.conj()) + np.outer(h, v.conj()))
    return np.asarray(tangents)


class FixedCountRecord:
    """Provide the same possible record under different simulator truths."""

    def __init__(self):
        self.calls = 0

    def multinomial(self, copies, probabilities):
        result = np.zeros(len(probabilities), dtype=np.int64)
        result[(13 * self.calls) % len(probabilities)] = copies
        self.calls += 1
        return result


class MixedPaperAlgorithmTests(unittest.TestCase):
    def test_exact_reference_and_pole_axes(self):
        eye = np.eye(3)
        axes, probabilities = mixed.measurement_design(np.zeros(3), "bures")
        np.testing.assert_array_equal(axes, eye[[2, 0, 1]])
        np.testing.assert_allclose(probabilities, np.ones(3) / 3)
        axes, _ = mixed.measurement_design(np.array([0.0, 0.0, 0.5]), "bures")
        np.testing.assert_array_equal(axes, eye[[2, 0, 1]])
        axes, _ = mixed.measurement_design(np.array([0.0, 0.0, -0.5]), "bures")
        np.testing.assert_array_equal(axes, np.array([-eye[2], eye[0], eye[1]]))

    def test_generic_radial_transverse_axes_and_allocation(self):
        c = np.array([0.1, 0.2, 0.3])
        axes, probabilities = mixed.measurement_design(c, "frobenius")
        np.testing.assert_allclose(axes @ axes.T, np.eye(3), atol=1e-14)
        np.testing.assert_allclose(axes[0], c / np.linalg.norm(c), atol=1e-14)
        s = np.sqrt(1 - c @ c)
        np.testing.assert_allclose(probabilities, np.array([s, 1, 1]) / (2 + s))

    def test_bures_open_ball_reset(self):
        inside = np.array([0.99, 0.0, 0.0])
        np.testing.assert_array_equal(mixed.design_estimate(inside, 5, "bures"), inside)
        for raw in (np.array([1.0, 0.0, 0.0]), np.array([1.2, 0.0, 0.0])):
            np.testing.assert_array_equal(mixed.design_estimate(raw, 5, "bures"), np.zeros(3))

    def test_frobenius_radius_and_initial_safeguard(self):
        raw = np.array([2.0, 0.0, 0.0])
        np.testing.assert_array_equal(mixed.design_estimate(raw, 0, "frobenius"), np.zeros(3))
        np.testing.assert_allclose(mixed.design_estimate(raw, 3, "frobenius"), [1 / np.sqrt(2), 0, 0])
        inside = np.array([0.1, 0.2, 0.0])
        np.testing.assert_array_equal(mixed.design_estimate(inside, 3, "frobenius"), inside)

    def test_scalar_losses_equal_physical_matrix_losses(self):
        paulis = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)
        truth = 0.9 * np.array([1, 2, 3]) / np.sqrt(14)
        c = np.array([-0.2, 0.1, 0.3])
        rho = (np.eye(2) + np.einsum("k,kij->ij", truth, paulis)) / 2
        estimate = (np.eye(2) + np.einsum("k,kij->ij", c, paulis)) / 2
        root = hermitian_square_root(rho)
        bures = 2 - 2 * np.trace(hermitian_square_root(root @ estimate @ root)).real
        expected = [np.linalg.norm(estimate - rho) ** 2, bures]
        np.testing.assert_allclose(mixed.physical_losses(c, truth, 1), expected, atol=2e-14)

    def test_fixed_records_do_not_use_truth_for_selection(self):
        truth_a = np.array([0.1, 0.2, 0.3])
        truth_b = np.array([-0.2, 0.1, 0.4])
        horizons = np.array([256, 512])
        for rule in ("bures", "frobenius"):
            _, rows_a = mixed.trajectory(rule, truth_a, FixedCountRecord(), horizons, diagnostic=True)
            _, rows_b = mixed.trajectory(rule, truth_b, FixedCountRecord(), horizons, diagnostic=True)
            for a, b in zip(rows_a, rows_b):
                for key in ("raw_estimate", "design_estimate", "next_axes", "next_probabilities"):
                    np.testing.assert_allclose(a[key], b[key], atol=1e-14)

    def test_unreachable_or_unordered_horizons_are_rejected(self):
        truth = np.array([0.1, 0.2, 0.3])
        for horizons in (np.array([]), np.array([17]), np.array([256, 300]), np.array([512, 256])):
            with self.subTest(horizons=horizons.tolist()):
                with self.assertRaises(ValueError):
                    mixed.trajectory("bures", truth, np.random.default_rng(13), horizons)


class PurePaperAlgorithmTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dimension = 4
        cls.reference, cls.bases, cls.labels = pure.reference_measurement(4)
        cls.truth = np.sqrt(np.arange(1, 5)) * np.exp(0.37j * np.arange(4))
        cls.truth /= np.linalg.norm(cls.truth)
        cls.hermitian_basis = estimators.hermitian_basis(4)
        cls.batches = []
        cls.individual_records = []
        rng = np.random.default_rng(981022)
        for copies in (16, 32):
            h = rng.normal(size=4) + 1j * rng.normal(size=4)
            h /= np.linalg.norm(h)
            unitary = estimators.householder_frame(h)
            effects = unitary @ cls.reference @ unitary.conj().T
            probabilities = np.array([np.vdot(cls.truth, effect @ cls.truth).real for effect in effects])
            counts = rng.multinomial(copies, probabilities / probabilities.sum())
            cls.batches.append(estimators.OutcomeBatch(effects, counts))
            cls.individual_records.extend((effects, label) for label, count in enumerate(counts) for _ in range(int(count)))

    def test_householder_first_column_and_unitarity(self):
        h = np.array([0.2 + 0.3j, -0.1, 0.4j, 0.7])
        h /= np.linalg.norm(h)
        unitary = estimators.householder_frame(h)
        np.testing.assert_allclose(unitary[:, 0], h, atol=1e-14)
        np.testing.assert_allclose(unitary.conj().T @ unitary, np.eye(4), atol=1e-14)

    def test_fixed_largest_algebraic_eigenvalue_ties_and_phase(self):
        np.testing.assert_array_equal(estimators.top_vector(np.eye(4)), [1, 0, 0, 0])
        np.testing.assert_array_equal(estimators.top_vector(np.diag([0.0, 2.0, 2.0, 0.0])), [0, 1, 0, 0])
        np.testing.assert_array_equal(estimators.top_vector(np.diag([-7.0, -2.0, -1.0])), [0, 0, 1])
        np.testing.assert_array_equal(estimators.top_vector(np.diag([2.0, 2.0 + 1e-12, 0.0])), [0, 1, 0])
        h = np.array([0.2j, -0.5, 0.3 + 0.1j, 0.7j])
        h /= np.linalg.norm(h)
        chosen = estimators.top_vector(projector(h))
        pivot = np.argmax(abs(chosen))
        self.assertAlmostEqual(chosen[pivot].imag, 0.0, places=14)
        self.assertGreater(chosen[pivot].real, 0)
        np.testing.assert_allclose(projector(chosen), projector(h), atol=1e-14)

    def test_complete_reference_law_and_label_probabilities(self):
        self.assertEqual(self.reference.shape, (104, 4, 4))
        self.assertEqual(self.bases.shape, (13, 4, 4))
        self.assertEqual(self.labels.shape, (104, 3))
        np.testing.assert_allclose(self.reference.sum(0), np.eye(4), atol=2e-14)
        unitary = estimators.householder_frame(self.truth)
        effects = unitary @ self.reference @ unitary.conj().T
        probabilities = np.array([np.vdot(self.truth, effect @ self.truth).real for effect in effects])
        np.testing.assert_allclose(probabilities.reshape(2, 13, 4).sum(2), np.full((2, 13), 1 / 26), atol=1e-14)
        phase_gate = np.diag([1j, 1, 1, 1])
        for index, (branch, basis, readout) in enumerate(self.labels):
            vector = self.bases[basis, :, readout]
            if branch:
                vector = phase_gate.conj().T @ vector
            np.testing.assert_allclose(self.reference[index], projector(vector) / 26, atol=1e-15)

    def test_reference_fisher_and_fixed_floor(self):
        e0 = np.eye(4, dtype=complex)[:, 0]
        tangents = []
        for phase in (1, 1j):
            for vector in np.eye(4, dtype=complex)[:, 1:].T:
                v = phase * vector / np.sqrt(2)
                tangents.append(np.outer(v, e0.conj()) + np.outer(e0, v.conj()))
        probabilities = np.array([np.vdot(e0, effect @ e0).real for effect in self.reference])
        gradients = np.array([[np.trace(effect @ tangent).real for tangent in tangents] for effect in self.reference])
        information = sum(np.outer(g, g) / probability for g, probability in zip(gradients, probabilities))
        np.testing.assert_allclose(information, np.eye(6), atol=1e-14)
        self.assertAlmostEqual(probabilities.min() / 4, 1 / 6240, places=17)

    def test_expanded_individual_record_ridge_objective(self):
        ridge = 0.7
        matrix = ridge * np.eye(16)
        rhs = np.zeros(16)
        for effects, outcome in self.individual_records:
            features = np.array([[np.trace(effect @ basis).real for basis in self.hermitian_basis] for effect in effects])
            matrix += features.T @ features
            rhs += features[outcome]
        coefficients = np.linalg.solve(matrix, rhs)
        raw = sum(coefficient * basis for coefficient, basis in zip(coefficients, self.hermitian_basis))
        fitted = estimators.least_squares_from_batches(self.batches, 4, ridge=ridge)
        np.testing.assert_allclose(fitted["raw"], raw, atol=1e-13)
        self.assertEqual(fitted["copies_used"], 48)

    def test_expanded_independent_complement_tangent_objective(self):
        eta = 1.4
        preliminary = estimators.least_squares_from_batches(self.batches, 4, ridge=0.7)
        h = preliminary["vector"]
        P = projector(h)
        tangents = independent_tangent_basis(h)
        np.testing.assert_allclose(np.einsum("kij,lji->kl", tangents, tangents).real, np.eye(6), atol=1e-14)
        matrix = eta * np.eye(6)
        score = np.zeros(6)
        floor = self.reference[:, 0, 0].real.min() / 4
        for effects, outcome in self.individual_records:
            for label, effect in enumerate(effects):
                gradient = np.array([np.trace(effect @ tangent).real for tangent in tangents])
                probability = np.trace(P @ effect).real
                residual = float(label == outcome) - probability
                denominator = max(probability, floor)
                matrix += np.outer(gradient, gradient) / denominator
                score += gradient * residual / denominator
        coordinates = np.linalg.solve(matrix, score)
        delta = sum(coordinate * tangent for coordinate, tangent in zip(coordinates, tangents))
        vector = h + delta @ h
        vector /= np.linalg.norm(vector)
        assembled = pure.correction(h, self.batches, self.reference, ridge=eta)
        direct = estimators.weighted_tangent_update(h, self.batches, self.reference, ridge=eta)
        np.testing.assert_allclose(projector(assembled), projector(vector), atol=1e-12)
        np.testing.assert_allclose(direct["state"], projector(vector), atol=1e-12)
        self.assertEqual(direct["copies_used"], 48)

    def test_all_record_order_invariance(self):
        forward = estimators.symmetric_gls_estimate(self.batches, self.reference)
        backward = estimators.symmetric_gls_estimate(list(reversed(self.batches)), self.reference)
        np.testing.assert_allclose(forward["initial"]["raw"], backward["initial"]["raw"], atol=1e-13)
        np.testing.assert_allclose(forward["state"], backward["state"], atol=1e-12)

    def test_pure_physical_loss_identity(self):
        vector = np.array([0.2j, -0.5, 0.3 + 0.1j, 0.7j])
        vector /= np.linalg.norm(vector)
        overlap = abs(np.vdot(self.truth, vector))
        frobenius, bures = pure.physical_losses(self.truth, vector, 1)
        self.assertAlmostEqual(bures, 2 * (1 - overlap), places=14)
        self.assertAlmostEqual(frobenius, 2 * (1 - overlap ** 2), places=14)

    def test_fixed_records_do_not_use_truth_for_alignment(self):
        other_truth = np.array([0.2j, -0.5, 0.3 + 0.1j, 0.7j])
        other_truth /= np.linalg.norm(other_truth)
        original = pure.preliminary
        histories = []
        for truth in (self.truth, other_truth):
            choices = []
            def record_preliminary(*args):
                vector = original(*args)
                choices.append(projector(vector))
                return vector
            with patch.object(pure, "preliminary", side_effect=record_preliminary):
                pure.trajectory(4, self.reference, truth, FixedCountRecord(), np.array([256, 512]))
            histories.append(choices)
        np.testing.assert_allclose(histories[0], histories[1], atol=1e-14)

    def test_optional_reference_sandwich_targets(self):
        for dimension in (2, 4):
            checks = optional.check_reference(optional.reference_measurement(dimension))
            self.assertLess(checks["completeness_error"], 1e-12)
            self.assertLess(checks["fisher_identity_error"], 1e-12)
            self.assertLess(checks["sandwich_target_error"], 1e-12)

    def test_unreachable_or_unordered_horizons_are_rejected(self):
        for horizons in (np.array([]), np.array([17]), np.array([256, 300]), np.array([512, 256])):
            with self.subTest(horizons=horizons.tolist()):
                with self.assertRaises(ValueError):
                    pure.trajectory(4, self.reference, self.truth, np.random.default_rng(13), horizons)


if __name__ == "__main__":
    unittest.main()
