"""Predetermined batch sizes and reporting at actual completed batches."""
import numpy as np


def batch_sizes(maximum, kind="growing", initial=16, minimum=16, denominator=50):
    """Make the complete schedule before sampling; truncate only its last batch.

    Growing blocks have nominal size max(minimum, ceil(N / denominator)).
    The minimum and integer budget are experimental choices, not data-dependent
    stopping rules. Doubling is retained for the supplementary comparison.
    """
    if any(not isinstance(v, (int, np.integer)) for v in (maximum, initial, minimum, denominator)):
        raise ValueError("Schedule parameters must be integers.")
    if maximum < initial or min(initial, minimum, denominator) <= 0:
        raise ValueError("Require positive parameters and a budget at least the initial size.")
    if kind not in ("growing", "doubling"):
        raise ValueError("Unknown batch schedule.")
    sizes, total = [], 0
    while total < maximum:
        nominal = initial if total == 0 else (
            max(minimum, (total + denominator - 1) // denominator)
            if kind == "growing" else total
        )
        size = min(nominal, maximum - total)
        sizes.append(size)
        total += size
    return np.asarray(sizes, dtype=np.int64)


def nearest_reporting_horizons(sizes, targets):
    """Choose nearest completed batches, without adding intermediate updates."""
    endpoints = np.cumsum(sizes)
    targets = np.asarray(targets)
    if (targets.ndim != 1 or len(targets) == 0
            or not np.issubdtype(targets.dtype, np.integer)
            or np.any(np.diff(targets) <= 0)
            or targets[0] < endpoints[0] or targets[-1] > endpoints[-1]):
        raise ValueError("Reporting targets must increase within the acquired range.")
    return np.unique([endpoints[np.argmin(abs(endpoints - target))] for target in targets])


def validated_batch_sizes(sizes, horizons):
    """Reject unreachable reports rather than silently returning zero entries."""
    if sizes is None:
        if np.any((horizons & (horizons - 1)) != 0):
            raise ValueError("Default doubling batches require power-of-two horizons.")
        sizes = batch_sizes(int(horizons[-1]), kind="doubling")
    sizes = np.asarray(sizes)
    if (sizes.ndim != 1 or len(sizes) == 0
            or not np.issubdtype(sizes.dtype, np.integer) or np.any(sizes <= 0)
            or sizes[0] != 16 or sizes.sum() != horizons[-1]
            or not np.all(np.isin(horizons, np.cumsum(sizes)))):
        raise ValueError("Positive batches must start at 16, exhaust the budget and reach every report.")
    return sizes.astype(np.int64, copy=False)
