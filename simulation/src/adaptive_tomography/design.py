"""Monte Carlo means of per-record pure-state information criteria.

The inverse is evaluated separately on every record before averaging. This
module replays every original Algorithm 3 loss stream, without seed selection.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import platform
import sys
import time
import numpy as np
from . import pure


COLUMNS = ['current_bures', 'average_bures']


def _sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def criteria_from_rows(rows):
    return np.asarray([[row[key] for key in COLUMNS] for row in rows])


def summarize(criteria, horizons):
    criteria = np.asarray(criteria, dtype=float)
    if criteria.ndim != 3 or criteria.shape[1:] != (len(horizons), 2):
        raise ValueError('Require (replicate, horizon, criterion) with two criteria.')
    if len(criteria) < 2 or not np.all(np.isfinite(criteria)):
        raise ValueError('Require at least two finite independent replicates.')
    mean = criteria.mean(axis=0)
    se = criteria.std(axis=0, ddof=1) / np.sqrt(len(criteria))
    return [{'n': int(n), 'mean': mean[i].tolist(), 'mc_se': se[i].tolist()}
            for i, n in enumerate(horizons)]


def save_design(results_directory, criteria, metadata=None):
    """Save criterion samples and arithmetic means, preserving the loss files."""
    directory = Path(results_directory)
    report = json.loads((directory / 'results.json').read_text())
    horizons = np.asarray(report['horizons'], dtype=np.int64)
    R = report['replications']
    if criteria.shape != (R, len(horizons), 2):
        raise ValueError('Design samples must cover every original loss replicate.')
    if np.any(criteria < report['oracle_constants']['pure_bures'] - 1e-9):
        raise ValueError('A per-record information criterion violates its bound.')
    summary = {
        'replications': R, 'horizons': horizons.tolist(), 'columns': COLUMNS,
        'aggregation': 'Arithmetic mean of the separately inverted per-record information criteria',
        'seed_sequence_pattern': [report['configuration']['root_seed'], 3, 1, 'replicate'],
        'replicate_indices': [0, R - 1], 'same_records_as_pure_loss_panel': True,
        'seed_selection': False, 'smoothing_or_monotonicity_enforcement': False,
        'pointwise_MC_error_band_multiplier': report['pointwise_MC_error_bar_multiplier'],
        'rows': summarize(criteria, horizons),
    }
    np.savez_compressed(directory / 'pure_design_samples.npz',
                        criteria=criteria, horizons=horizons)
    (directory / 'pure_design_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    module = Path(__file__).resolve().parent
    files = ['pure.py', 'estimators.py', 'schedules.py', 'design.py']
    receipt = {
        'status': 'PASS', 'completed_utc': datetime.now(timezone.utc).isoformat(),
        'replications': R, 'root_seed_unchanged': True,
        'all_original_loss_streams_used': True,
        'source_sha256': {f'src/adaptive_tomography/{name}':
                          _sha(module / name) for name in files},
        'base_output_sha256': {name: _sha(directory / name)
                              for name in ['results.json', 'samples.npz', 'apparatus.npz']},
        'output_sha256': {name: _sha(directory / name)
                         for name in ['pure_design_samples.npz', 'pure_design_summary.json']},
        'Python': sys.version, 'NumPy': np.__version__, 'platform': platform.platform(),
    }
    receipt.update(metadata or {})
    (directory / 'pure_design_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return summary


def replay_pure_design(results_directory):
    """Replay all saved pure loss streams and verify every loss/tangent error."""
    directory = Path(results_directory)
    report = json.loads((directory / 'results.json').read_text())
    original = json.loads((directory / 'run_receipt.json').read_text())
    for name, expected in original['output_sha256'].items():
        if _sha(directory / name) != expected:
            raise ValueError(f'Original numerical output changed: {name}')
    module = Path(__file__).resolve().parent
    names = [f'src/adaptive_tomography/{name}'
             for name in ['pure.py', 'estimators.py', 'schedules.py']]
    for name in names:
        if _sha(module / Path(name).name) != original['source_sha256'][name]:
            raise ValueError(f'Estimator or observation implementation changed: {name}')
    locked = {name: _sha(module / Path(name).name) for name in names +
              ['src/adaptive_tomography/design.py']}
    with np.load(directory / 'samples.npz', allow_pickle=False) as data:
        losses = data['pure_losses']
        errors = data['pure_tangent_errors']
    with np.load(directory / 'apparatus.npz', allow_pickle=False) as data:
        truth, reference = data['pure_truth'], data['pure_reference']
    config = report['configuration']
    horizons = np.asarray(report['horizons'], dtype=np.int64)
    sizes = np.asarray(report['main_batch_sizes'], dtype=np.int64)
    R, D = report['replications'], config['pure_dimension']
    samples = np.empty((R, len(horizons), 2))
    max_loss_error = max_tangent_error = 0.0
    started = datetime.now(timezone.utc).isoformat()
    tick = time.perf_counter()
    for rep in range(R):
        rng = np.random.default_rng(np.random.SeedSequence([config['root_seed'], 3, 1, rep]))
        replay_losses, replay_errors, rows = pure.trajectory(
            D, reference, truth, rng, horizons, diagnostic=True,
            ridge=config['ridge'], correction_ridge=config['correction_ridge'],
            batch_sizes=sizes)
        max_loss_error = max(max_loss_error, float(np.max(abs(replay_losses - losses[rep]))))
        max_tangent_error = max(max_tangent_error, float(np.max(abs(replay_errors - errors[rep]))))
        # Identical algorithms/streams can differ at roundoff level after
        # eigensolver and diagnostic BLAS calls. Reject substantive changes.
        np.testing.assert_allclose(replay_losses, losses[rep], rtol=1e-10, atol=1e-10)
        np.testing.assert_allclose(replay_errors, errors[rep], rtol=1e-10, atol=1e-10)
        if [row['n'] for row in rows] != horizons.tolist():
            raise ValueError('Diagnostic reporting sizes do not match the loss panel.')
        samples[rep] = criteria_from_rows(rows)
        if (rep + 1) % 256 == 0 or rep + 1 == R:
            progress = {'completed_replicates': rep + 1, 'replications': R,
                        'elapsed_seconds': round(time.perf_counter() - tick, 2)}
            (directory / 'pure_design_progress.json').write_text(json.dumps(progress, indent=2) + '\n')
            print(json.dumps(progress), flush=True)
    if any(_sha(module / Path(name).name) != expected for name, expected in locked.items()):
        raise RuntimeError('Diagnostic or estimator source changed during execution.')
    summary = save_design(directory, samples, {
        'started_utc': started, 'seconds': time.perf_counter() - tick,
        'fresh_exact_Born_replay': True, 'all_saved_pure_losses_reproduced': True,
        'all_saved_pure_tangent_errors_reproduced': True,
        'maximum_absolute_loss_replay_difference': max_loss_error,
        'maximum_absolute_tangent_replay_difference': max_tangent_error,
        'replay_comparison_tolerance': {'rtol': 1e-10, 'atol': 1e-10},
        'original_individual_count_records_saved': False,
        'replay_evidence': 'Original random streams and algorithms replayed; every stored loss and tangent error matches to the stated tolerance.',
        'estimator_sources_identical_to_original_run': True,
    })
    print(json.dumps({'status': 'PASS', 'final_design': summary['rows'][-1]}), flush=True)
    return summary
