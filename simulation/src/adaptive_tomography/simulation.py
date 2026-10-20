"""Reproduce the two main-paper figures and optional covariance experiment."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import platform
import sys
import time
import numpy as np
from . import __version__, mixed, pure, optional
from .schedules import batch_sizes, nearest_reporting_horizons


def _write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def _summary(losses, horizons):
    R = len(losses)
    return [{'n':int(n),'mean':losses[:,i].mean(0).tolist(),
             'mc_se':(losses[:,i].std(0,ddof=1)/np.sqrt(R)).tolist()}
            for i,n in enumerate(horizons)]


def _covariance_summary(errors, losses, horizons):
    R, _, _, p = errors.shape
    rows = []
    for i,n in enumerate(horizons):
        row = {'n':int(n)}
        squared = []
        for method,name in enumerate(['uncorrected','corrected']):
            x = errors[:,i,method]
            centered = x-x.mean(0)
            covariance = centered.T@centered/(R-1)
            contributions = (centered*centered).sum(1)/p*R/(R-1)
            squared.append((x*x).sum(1)/p)
            values = losses[:,i,method]
            row[name] = {'mean_tangent_variance':float(np.trace(covariance)/p),
                'variance_mc_se':float(contributions.std(ddof=1)/np.sqrt(R)),
                'covariance_eigenvalues':np.linalg.eigvalsh(covariance).tolist(),
                'scaled_bias_norm':float(np.linalg.norm(x.mean(0))),
                'mean_n_frobenius_loss':float(values[:,0].mean()),
                'frobenius_loss_mc_se':float(values[:,0].std(ddof=1)/np.sqrt(R)),
                'mean_n_bures_loss':float(values[:,1].mean()),
                'bures_loss_mc_se':float(values[:,1].std(ddof=1)/np.sqrt(R)),
                'frobenius_loss_99th_percentile':float(np.quantile(values[:,0],.99))}
        paired = squared[0]-squared[1]
        row['paired_tangent_MSE_difference'] = float(paired.mean())
        row['paired_difference_mc_se'] = float(paired.std(ddof=1)/np.sqrt(R))
        rows.append(row)
    return rows


def run(config, output):
    """Execute every configured experiment, preserving all replicate losses.

    SeedSequence [root_seed, experiment, role, replication] separates each
    replicate. Role 0 is a separate diagnostic history; role 1 is Monte Carlo.
    The pure design panel averages the criteria on every role-1 loss record.
    Experiments 1/2 are mixed Bures/Frobenius, 3 is Algorithm 3, and 4/5
    are optional D=2/D=4 covariance comparisons. No stream is selected by results.
    """
    output = Path(output)
    output.mkdir(parents=True,exist_ok=True)
    module = Path(__file__).resolve().parent
    source_files = {f'src/adaptive_tomography/{f.name}':f for f in module.glob('*.py')}
    source_hashes = {name:hashlib.sha256(f.read_bytes()).hexdigest()
                     for name,f in source_files.items()}
    config_digest = hashlib.sha256(json.dumps(config,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    R = int(config['replications'])
    if R < 2 or config['main_batch_schedule']['initial'] != 16:
        raise ValueError('Require at least two Monte Carlo replicates and the paper first batch of 16.')
    if config['ridge'] <= 0 or config['correction_ridge'] <= 0:
        raise ValueError('Ridge parameters must be positive.')
    if config['pure_dimension'] != 4 or config['main_horizontal_axis'] != 'linear':
        raise ValueError('This paper configuration uses D=4 and a linear main horizontal axis.')
    sizes = batch_sizes(**config['main_batch_schedule'])
    maximum = int(sizes.sum())
    targets = [int(n) for n in config['main_reporting_targets'] if n <= maximum]
    if not targets or targets[-1] != maximum:
        targets.append(maximum)
    horizons = nearest_reporting_horizons(sizes, targets)
    if config['optional_batch_schedule'] != 'doubling':
        raise ValueError('The supplementary covariance comparison retains doubling batches.')
    seed = int(config['root_seed'])
    started = datetime.now(timezone.utc).isoformat()
    beginning = time.perf_counter()
    arrays, apparatus, studies, timings = {}, {}, {}, {}
    progress_file = output/'progress.json'
    def rng(experiment,role,replication):
        return np.random.default_rng(np.random.SeedSequence([seed,experiment,role,replication]))
    def progress(study,done):
        value={'study':study,'completed_replicates':done,'replications':R,
               'elapsed_seconds':round(time.perf_counter()-beginning,2)}
        _write(progress_file,value)
        print(json.dumps(value),flush=True)
    direction = np.array(config['mixed_truth_direction'],dtype=float)
    mixed_truth = config['mixed_truth_radius']*direction/np.linalg.norm(direction)
    if np.linalg.norm(mixed_truth) >= 1:
        raise ValueError('Mixed truth must be interior.')
    for experiment,rule in [(1,'bures'),(2,'frobenius')]:
        tick = time.perf_counter()
        _,diagnostics = mixed.trajectory(rule,mixed_truth,rng(experiment,0,0),horizons,
                                         config['ridge'],diagnostic=True,batch_sizes=sizes)
        values = np.empty((R,len(horizons),2))
        for rep in range(R):
            values[rep],_ = mixed.trajectory(rule,mixed_truth,rng(experiment,1,rep),
                                             horizons,config['ridge'],batch_sizes=sizes)
            if (rep+1)%256 == 0 or rep+1 == R:progress('mixed_'+rule,rep+1)
        arrays['mixed_'+rule+'_losses'] = values
        studies['mixed_'+rule] = {'experiment_id':experiment,'dimension':2,'qubits':1,
            'truth':mixed_truth.tolist(),'diagnostics':diagnostics,'risks':_summary(values,horizons)}
        timings['mixed_'+rule] = time.perf_counter()-tick
    D = config['pure_dimension']
    truth = np.sqrt(np.arange(1,D+1))*np.exp(1j*config['pure_truth_phase_increment']*np.arange(D))
    truth /= np.linalg.norm(truth)
    reference,bases,labels = pure.reference_measurement(D)
    reference_checks = pure.validate_reference(reference,bases,truth)
    apparatus.update({'pure_reference':reference,'pure_reference_bases':bases,
                      'pure_labels':labels,'pure_truth':truth,'mixed_truth':mixed_truth})
    tick = time.perf_counter()
    _,_,diagnostics = pure.trajectory(D,reference,truth,rng(3,0,0),horizons,
        diagnostic=True,validate=True,ridge=config['ridge'],correction_ridge=config['correction_ridge'],batch_sizes=sizes)
    values = np.empty((R,len(horizons),2,2))
    errors = np.empty((R,len(horizons),2,2*(D-1)))
    design_values = np.empty((R,len(horizons),2))
    from .design import criteria_from_rows, save_design
    for rep in range(R):
        values[rep],errors[rep],design_rows = pure.trajectory(D,reference,truth,rng(3,1,rep),horizons,
            diagnostic=True,ridge=config['ridge'],correction_ridge=config['correction_ridge'],batch_sizes=sizes)
        design_values[rep] = criteria_from_rows(design_rows)
        if (rep+1)%256 == 0 or rep+1 == R:progress('pure_algorithm3',rep+1)
    arrays.update({'pure_losses':values,'pure_tangent_errors':errors})
    studies['pure_algorithm3'] = {'experiment_id':3,'dimension':D,'qubits':2,
        'truth_real':truth.real.tolist(),'truth_imag':truth.imag.tolist(),
        'reference_bases':len(bases),'complete_labelled_outcomes':len(reference),
        'probability_floor':float(reference[:,0,0].real.min()/4),
        'reference_validation':reference_checks,'diagnostics':diagnostics,'risks':_summary(values,horizons)}
    timings['pure_algorithm3'] = time.perf_counter()-tick
    optional_powers = [k for k in config['optional_reporting_powers'] if k<=config['optional_maximum_reporting_power']]
    optional_horizons = np.array([2**k for k in optional_powers] or [int(horizons[-1])],dtype=np.int64)
    for D in config['optional_covariance_dimensions']:
        if D not in [2,4]:raise ValueError('Optional covariance dimensions are 2 and 4.')
        experiment = 4 if D==2 else 5
        tick = time.perf_counter()
        reference = optional.reference_measurement(D)
        checks = optional.check_reference(reference)
        truth = np.sqrt(np.arange(1,D+1))*np.exp(1j*config['pure_truth_phase_increment']*np.arange(D))
        truth /= np.linalg.norm(truth)
        pure.trajectory(D,reference,truth,rng(experiment,0,0),optional_horizons,
            validate=True,ridge=config['ridge'],correction_ridge=config['correction_ridge'])
        values = np.empty((R,len(optional_horizons),2,2))
        errors = np.empty((R,len(optional_horizons),2,2*(D-1)))
        for rep in range(R):
            values[rep],errors[rep],_ = pure.trajectory(D,reference,truth,rng(experiment,1,rep),
                optional_horizons,ridge=config['ridge'],correction_ridge=config['correction_ridge'])
            if (rep+1)%256 == 0 or rep+1 == R:progress('optional_D'+str(D),rep+1)
        arrays.update({f'optional_D{D}_losses':values,f'optional_D{D}_tangent_errors':errors})
        apparatus.update({f'optional_D{D}_reference':reference,f'optional_D{D}_truth':truth})
        studies[f'optional_D{D}'] = {'experiment_id':experiment,'dimension':D,
            'truth_real':truth.real.tolist(),'truth_imag':truth.imag.tolist(),
            'reference_validation':checks,'variance_target_uncorrected':4*(D-1)*(5*D-7)/(4*D-5)**2,
            'variance_target_corrected':1.0,'risks':_covariance_summary(errors,values,optional_horizons)}
        timings[f'optional_D{D}'] = time.perf_counter()-tick
    s0 = np.sqrt(1-mixed_truth@mixed_truth)
    result = {'package_version':__version__,'configuration':config,'replications':R,
        'horizons':horizons.tolist(),'optional_horizons':optional_horizons.tolist(),
        'seed_sequence_pattern':['root_seed','experiment_id','role','replication'],
        'role_definition':{'0':'separate diagnostic history','1':'independent Monte Carlo replicate'},
        'main_batch_sizes':sizes.tolist(),'main_batch_endpoints':np.cumsum(sizes).tolist(),
        'main_reporting_targets':targets,'main_horizontal_axis':config['main_horizontal_axis'],
        'optional_batch_schedule':'doubling',
        'actual_loss_order':['squared_frobenius','squared_Bures'],
        'pure_method_order':['uncorrected_preliminary','corrected_reported'],
        'oracle_constants':{'mixed_frobenius':float((2+s0)**2/2),'mixed_bures':2.25,'pure_bures':3.0},
        'studies':studies,'pointwise_MC_error_bar_multiplier':config['error_bar_multiplier'],
        'all_acquired_copies_counted':True,'replicates_reused_across_horizons':True,
        'sampling':'exact conditional setting-outcome multinomial counts, not an estimator approximation',
        'scope':'Fixed truths; predetermined 2%-growth main batches with a 16-copy minimum and final budget clipping, and doubling supplementary batches. Numerical evidence, not a uniform risk claim.'}
    arrays.update({'horizons':horizons,'optional_horizons':optional_horizons,
                   'main_batch_sizes':sizes,'main_batch_endpoints':np.cumsum(sizes)})
    np.savez_compressed(output/'samples.npz',**arrays)
    np.savez_compressed(output/'apparatus.npz',**apparatus)
    _write(output/'results.json',result)
    save_design(output,design_values,{'fresh_joint_simulation':True,
        'same_simulation_call_as_loss_panel':True})
    assert all(hashlib.sha256(source_files[name].read_bytes()).hexdigest()==digest
               for name,digest in source_hashes.items()),'Simulation source changed during execution.'
    receipt={'status':'PASS','started_utc':started,'completed_utc':datetime.now(timezone.utc).isoformat(),
        'seconds':time.perf_counter()-beginning,'study_seconds':timings,'replications_per_study':R,
        'fresh_simulation':True,'Python':sys.version,'NumPy':np.__version__,'platform':platform.platform(),
        'configuration':config,'configuration_sha256':config_digest,
        'source_sha256':source_hashes,'source_unchanged_during_execution':True,
        'output_sha256':{name:hashlib.sha256((output/name).read_bytes()).hexdigest()
                         for name in ['results.json','samples.npz','apparatus.npz']}}
    _write(output/'run_receipt.json',receipt)
    _write(progress_file,{'phase':'complete','replications':R,'seconds':receipt['seconds']})
    print(json.dumps({'status':'PASS','seconds':receipt['seconds'],'output':str(output)}),flush=True)
    return result
