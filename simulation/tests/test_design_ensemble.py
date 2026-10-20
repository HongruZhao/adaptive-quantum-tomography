"""Independent checks of per-record inversion followed by Monte Carlo averaging."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest

import numpy as np

from adaptive_tomography import design


class DesignEnsembleTests(unittest.TestCase):
    def test_average_of_inverse_criteria_differs_from_inverse_of_mean_information(self):
        weight = np.eye(6)/2
        informations = [np.eye(6), np.eye(6)/2]
        current = [np.trace(weight@np.linalg.inv(value)) for value in informations]
        accumulated = [np.eye(6)*.8, np.eye(6)*.6]
        average = [np.trace(weight@np.linalg.inv(value)) for value in accumulated]
        values = np.asarray([[[c,a]] for c,a in zip(current,average)])
        result = design.summarize(values,[256])[0]
        np.testing.assert_allclose(result['mean'],[sum(current)/2,sum(average)/2])
        pooled_current = np.trace(weight@np.linalg.inv(sum(informations)/2))
        self.assertGreater(abs(result['mean'][0]-pooled_current),.4)
        expected_se=[abs(current[0]-current[1])/2,abs(average[0]-average[1])/2]
        np.testing.assert_allclose(result['mc_se'],expected_se,atol=1e-14)

    def test_every_replication_and_each_distinct_reporting_size_enters_summary(self):
        values=np.array([[[3.,4.],[4.,7.]],[[7.,8.],[5.,8.]],[[5.,15.],[9.,13.]]])
        original=values.copy()
        rows=design.summarize(values,[256,1020])
        for index,row in enumerate(rows):
            expected_mean=np.sum(values[:,index],axis=0)/3
            expected_variance=(np.sum(values[:,index]**2,axis=0)-3*expected_mean**2)/2
            np.testing.assert_allclose(row['mean'],expected_mean)
            np.testing.assert_allclose(row['mc_se'],np.sqrt(expected_variance/3))
        self.assertEqual([row['n'] for row in rows],[256,1020])
        np.testing.assert_array_equal(values,original)

    def test_summary_uses_unbiased_MCSE_without_forcing_monotonicity(self):
        values=np.array([[[3.,4.],[8.,9.]],[[5.,8.],[10.,15.]],[[7.,12.],[12.,21.]]])
        rows=design.summarize(values,[256,512])
        self.assertGreater(rows[1]['mean'][0],rows[0]['mean'][0])
        expected=np.sqrt(4/3)
        self.assertAlmostEqual(rows[0]['mc_se'][0],expected)
        self.assertNotAlmostEqual(rows[0]['mc_se'][0],np.std(values[:,0,0],ddof=0)/np.sqrt(3))

    def test_row_extraction_keeps_current_then_accumulated_order(self):
        rows=[{'n':256,'current_bures':3.1,'average_bures':3.8,'current_frobenius':6.2},
              {'n':1020,'current_bures':3.04,'average_bures':3.2,'current_frobenius':6.08}]
        np.testing.assert_array_equal(design.criteria_from_rows(rows),[[3.1,3.8],[3.04,3.2]])

    def test_nonfinite_or_incomplete_replicates_are_rejected(self):
        for values in (np.array([[[3.,4.]]]), np.ones((2,2,2)),
                       np.array([[[np.nan,4.]],[[3.,4.]]]),
                       np.array([[[np.inf,4.]],[[3.,4.]]])):
            with self.subTest(shape=values.shape),self.assertRaises(ValueError):
                design.summarize(values,[256])

    def test_saving_preserves_all_original_data_and_documents_aggregation(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            report={'horizons':[256,1020],'replications':3,'oracle_constants':{'pure_bures':3.},
                    'configuration':{'root_seed':2026101602},'pointwise_MC_error_bar_multiplier':1.96}
            (directory/'results.json').write_text(json.dumps(report))
            np.savez(directory/'samples.npz',sentinel=np.array([1,2,3]))
            np.savez(directory/'apparatus.npz',sentinel=np.eye(4))
            original={name:(directory/name).read_bytes() for name in ['results.json','samples.npz','apparatus.npz']}
            values=np.array([[[3.,4.],[4.,5.]],[[5.,6.],[6.,7.]],[[9.,10.],[10.,11.]]])
            summary=design.save_design(directory,values)
            self.assertEqual(summary['replications'],3)
            self.assertEqual(summary['seed_sequence_pattern'],[2026101602,3,1,'replicate'])
            self.assertEqual(summary['replicate_indices'],[0,2])
            self.assertFalse(summary['seed_selection'])
            self.assertFalse(summary['smoothing_or_monotonicity_enforcement'])
            self.assertIn('separately inverted',summary['aggregation'])
            for name,content in original.items():
                self.assertEqual((directory/name).read_bytes(),content)
            with np.load(directory/'pure_design_samples.npz',allow_pickle=False) as saved:
                np.testing.assert_array_equal(saved['criteria'],values)

    def test_fresh_run_then_design_replay_preserves_valid_base_receipt(self):
        from adaptive_tomography import simulation
        config={'replications':2,'root_seed':2026101602,'ridge':1.,'correction_ridge':1.,
                'mixed_truth_radius':.9,'mixed_truth_direction':[1.,2.,3.],
                'pure_dimension':4,'pure_truth_phase_increment':.37,
                'optional_covariance_dimensions':[2,4],'optional_reporting_powers':[12,16,20,24],
                'optional_maximum_reporting_power':10,'error_bar_multiplier':1.96,
                'main_batch_schedule':{'kind':'growing','initial':16,'minimum':16,'denominator':50,'maximum':1024},
                'main_reporting_targets':[256,512,1024],'main_horizontal_axis':'linear',
                'optional_batch_schedule':'doubling'}
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            with contextlib.redirect_stdout(io.StringIO()):
                simulation.run(config,directory)
            receipt=json.loads((directory/'run_receipt.json').read_text())
            self.assertEqual(set(receipt['output_sha256']),{'results.json','samples.npz','apparatus.npz'})
            self.assertIn('src/adaptive_tomography/design.py',receipt['source_sha256'])
            self.assertGreaterEqual(len(receipt['source_sha256']),10)
            config_hash=hashlib.sha256(json.dumps(config,sort_keys=True,separators=(',',':')).encode()).hexdigest()
            self.assertEqual(receipt['configuration_sha256'],config_hash)
            names=list(receipt['output_sha256'])+['run_receipt.json']
            original={name:(directory/name).read_bytes() for name in names}
            with contextlib.redirect_stdout(io.StringIO()):
                design.replay_pure_design(directory)
            for name,content in original.items():
                self.assertEqual((directory/name).read_bytes(),content)
            for name,digest in receipt['output_sha256'].items():
                self.assertEqual(hashlib.sha256((directory/name).read_bytes()).hexdigest(),digest)
            added=json.loads((directory/'pure_design_receipt.json').read_text())
            self.assertEqual(added['status'],'PASS')
            for name,digest in added['output_sha256'].items():
                self.assertEqual(hashlib.sha256((directory/name).read_bytes()).hexdigest(),digest)


if __name__=='__main__':
    unittest.main()
