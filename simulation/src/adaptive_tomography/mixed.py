"""Algorithms 1 and 2: all-record ridge fits and prescribed Pauli designs."""
import numpy as np
from .schedules import validated_batch_sizes
from .estimators import validated_horizons


def design_estimate(raw, n, rule):
    """Apply the paper's Bures reset or Frobenius ball projection."""
    radius = np.linalg.norm(raw)
    if rule == 'bures':
        return raw.copy() if radius < 1 else np.zeros(3)
    if rule != 'frobenius':
        raise ValueError('rule must be bures or frobenius')
    cap = np.sqrt(1 - (n + 1)**(-.5))
    return raw.copy() if radius <= cap else cap*raw/radius


def measurement_design(c, rule):
    """Exact e3-based Householder completion specified in the manuscript.

    Rows are radial first, then Q(c)e1 and Q(c)e2. At c=0 the
    reference triple is (e3,e1,e2), as in Algorithms 1 and 2.
    """
    eye = np.eye(3)
    radius = np.linalg.norm(c)
    if radius == 0:
        axes = eye[[2,0,1]]
    else:
        u = c/radius
        v = u-eye[:,2]
        Q = eye if np.array_equal(u,eye[:,2]) else eye-2*np.outer(v,v)/np.dot(v,v)
        axes = np.array([u,Q[:,0],Q[:,1]])
    if rule == 'bures':
        pi = np.full(3,1/3)
    elif rule == 'frobenius':
        s = np.sqrt(max(1-radius*radius,0))
        pi = np.array([s,1,1])/(2+s)
    else:
        raise ValueError('rule must be bures or frobenius')
    return axes,pi


def information(axes, pi, truth):
    means = axes@truth
    return np.einsum('k,ki,kj->ij',pi/(1-means*means),axes,axes)


def loss_weights(truth):
    H = np.eye(3)+np.outer(truth,truth)/(1-truth@truth)
    return {'frobenius':np.eye(3)/2,'bures':H/4}


def physical_losses(c, truth, n):
    """n times exact squared Frobenius and Bures losses of physical states."""
    frobenius = np.dot(c-truth,c-truth)/2
    fidelity = (1+c@truth+np.sqrt(max(1-c@c,0))*np.sqrt(1-truth@truth))/2
    fidelity = np.clip(fidelity,0,1)
    bures = 2*(1-fidelity)/(1+np.sqrt(fidelity))
    return np.array([n*frobenius,n*bures])


def trajectory(rule, truth, rng, horizons, ridge=1.0, diagnostic=False, batch_sizes=None):
    """One complete adaptive record, simulated by exact batch counts."""
    horizons = validated_horizons(horizons)
    sizes = validated_batch_sizes(batch_sizes, horizons)
    gram = ridge*np.eye(3)
    rhs = np.zeros(3)
    c = np.zeros(3)
    n = 0
    losses = np.zeros((len(horizons),2))
    accumulated = np.zeros((3,3))
    rows = []
    W = loss_weights(truth)[rule]
    for size in sizes.tolist():
        axes,pi = measurement_design(c,rule)
        means = axes@truth
        p = pi[:,None]*(1+means[:,None]*np.array([-1.,1.]))/2
        assert p.min() >= 0 and abs(p.sum()-1) < 1e-12
        counts = rng.multinomial(size,p.ravel()/p.sum()).reshape(3,2)
        if diagnostic:
            accumulated += size*information(axes,pi,truth)
        gram += np.einsum('k,ki,kj->ij',counts.sum(1),axes,axes)
        rhs += (counts[:,1]-counts[:,0])@axes
        n += size
        raw = np.linalg.solve(gram,rhs)
        c = design_estimate(raw,n,rule)
        if n not in horizons:
            continue
        ix = int(np.flatnonzero(horizons==n)[0])
        losses[ix] = physical_losses(c,truth,n)
        if diagnostic:
            next_axes,next_pi = measurement_design(c,rule)
            current = information(next_axes,next_pi,truth)
            average = accumulated/n
            rows.append({'n':n,'current':float(np.trace(np.linalg.solve(current,W))),
                'average':float(np.trace(np.linalg.solve(average,W))),
                'current_information':current.tolist(),'average_information':average.tolist(),
                'raw_estimate':raw.tolist(),'design_estimate':c.tolist(),
                'next_axes':next_axes.tolist(),'next_probabilities':next_pi.tolist()})
    return losses,rows
