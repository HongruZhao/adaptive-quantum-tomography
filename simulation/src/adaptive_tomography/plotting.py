"""Publication figures calculated only from stored simulation records."""
from pathlib import Path
import hashlib
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def render(results_directory, output):
    results_directory,output = Path(results_directory),Path(output)
    output.mkdir(parents=True,exist_ok=True)
    report = json.loads((results_directory/'results.json').read_text())
    R = report['replications']
    with np.load(results_directory/'samples.npz',allow_pickle=False) as saved:
        arrays = {name:saved[name] for name in saved.files}
    design_summary = json.loads((results_directory/'pure_design_summary.json').read_text())
    with np.load(results_directory/'pure_design_samples.npz',allow_pickle=False) as saved:
        design_values = saved['criteria']
        assert saved['horizons'].tolist() == report['horizons']
    assert design_values.shape == (R,len(report['horizons']),2)
    assert design_summary['replications'] == R
    assert design_summary['same_records_as_pure_loss_panel']
    assert not design_summary['seed_selection']
    assert np.all(design_values >= report['oracle_constants']['pure_bures']-1e-9)
    for i,row in enumerate(design_summary['rows']):
        assert row['n'] == report['horizons'][i]
        assert np.allclose(design_values[:,i].mean(0),row['mean'],rtol=1e-13,atol=1e-13)
        assert np.allclose(design_values[:,i].std(0,ddof=1)/np.sqrt(R),row['mc_se'],rtol=1e-13,atol=1e-13)
    for key in ['mixed_bures','mixed_frobenius','pure_algorithm3']:
        values = arrays['pure_losses' if key=='pure_algorithm3' else key+'_losses']
        for i,row in enumerate(report['studies'][key]['risks']):
            assert np.allclose(values[:,i].mean(0),row['mean'],rtol=1e-13,atol=1e-13)
            assert np.allclose(values[:,i].std(0,ddof=1)/np.sqrt(R),row['mc_se'],rtol=1e-13,atol=1e-13)
    for D in report['configuration']['optional_covariance_dimensions']:
        errors=arrays[f'optional_D{D}_tangent_errors']
        losses=arrays[f'optional_D{D}_losses']
        for i,row in enumerate(report['studies'][f'optional_D{D}']['risks']):
            squared=[]
            for method,name in enumerate(['uncorrected','corrected']):
                x=errors[:,i,method];p=x.shape[1]
                centered=x-x.mean(0)
                cov=np.cov(x,rowvar=False,ddof=1)
                contributions=np.linalg.norm(centered,axis=1)**2/p*R/(R-1)
                assert np.allclose(np.trace(cov)/p,row[name]['mean_tangent_variance'],rtol=1e-12)
                assert np.allclose(contributions.std(ddof=1)/np.sqrt(R),row[name]['variance_mc_se'],rtol=1e-12)
                assert np.allclose(np.linalg.eigvalsh(cov),row[name]['covariance_eigenvalues'],rtol=1e-12)
                assert np.allclose(np.linalg.norm(x.mean(0)),row[name]['scaled_bias_norm'],rtol=1e-12)
                for j,loss_name in enumerate(['frobenius','bures']):
                    assert np.allclose(losses[:,i,method,j].mean(),row[name]['mean_n_'+loss_name+'_loss'],rtol=1e-12)
                    assert np.allclose(losses[:,i,method,j].std(ddof=1)/np.sqrt(R),row[name][loss_name+'_loss_mc_se'],rtol=1e-12)
                squared.append(np.linalg.norm(x,axis=1)**2/p)
            paired=squared[0]-squared[1]
            assert np.allclose(paired.mean(),row['paired_tangent_MSE_difference'],rtol=1e-12)
            assert np.allclose(paired.std(ddof=1)/np.sqrt(R),row['paired_difference_mc_se'],rtol=1e-12)
    plt.rcParams.update({'font.family':'STIXGeneral','mathtext.fontset':'stix',
        'font.size':10.5,'axes.titlesize':10.5,'axes.labelsize':10.5,
        'legend.fontsize':9,'pdf.fonttype':42,'ps.fonttype':42,
        'axes.spines.top':False,'axes.spines.right':False})
    blue,orange,gray = '#0072B2','#D55E00','#777777'
    n = np.array(report['horizons'])
    error_multiplier = report['pointwise_MC_error_bar_multiplier']
    def frame(ax,horizons,constant,legend_location):
        ax.axhline(constant,color='black',ls=':',lw=1.2,label='Gill-Massar bound')
        ax.set_xscale('linear')
        ax.set_xlim(int(horizons[0]),int(horizons[-1]))
        ticks = [256,4096,8192,12288,16384]
        ticks = [value for value in ticks if horizons[0] <= value <= horizons[-1]]
        if len(ticks) < 2:
            ticks = np.linspace(horizons[0],horizons[-1],4,dtype=int).tolist()
        ax.set_xticks(ticks,[f'{value:,}' for value in ticks])
        ax.tick_params(axis='x',labelsize=9)
        ax.set_xlabel('Copies, $n$')
        ax.grid(alpha=.15)
        handles, labels = ax.get_legend_handles_labels()
        order = [i for i, label in enumerate(labels) if label != 'Gill-Massar bound']
        order += [i for i, label in enumerate(labels) if label == 'Gill-Massar bound']
        ax.legend([handles[i] for i in order], [labels[i] for i in order],
                  frameon=False,loc=legend_location,fontsize=9)
    def design(ax,rows,constant,pure_state=False):
        if pure_state:
            current=np.array([v['current_bures'] for v in rows])
            average=np.array([v['average_bures'] for v in rows])
        else:
            current=np.array([v['current'] for v in rows])
            average=np.array([v['average'] for v in rows])
        assert np.all(current>=constant-1e-9) and np.all(average>=constant-1e-9)
        ax.plot(n,current,color=blue,marker='o',ms=3,lw=1.1,
                label=r'$C_n^{\rm cur}$: current design')
        ax.plot(n,average,color=orange,marker='s',ms=2.8,lw=1.1,
                label=r'$C_n^{\rm avg}$: accumulated information')
        gap=max(float(max(current.max(),average.max())-constant),constant*.025)
        ax.set_ylim(constant-gap*.12,constant+gap*1.55)
        ax.set_ylabel(r'$\mathrm{tr}(W\mathcal{I}^{-1})$')
        frame(ax,n,constant,'upper right')
    def save(fig,name):
        fig.savefig(output/(name+'.pdf'),bbox_inches='tight')
        fig.savefig(output/(name+'.png'),dpi=200,bbox_inches='tight')
        plt.close(fig)
    fig,axes=plt.subplots(2,2,figsize=(7.1,5.8))
    for row,(loss,index,title) in enumerate([('frobenius',0,'Squared Frobenius'),('bures',1,'Squared Bures')]):
        left,right=axes[row]
        constant=report['oracle_constants']['mixed_'+loss]
        left.set_title(f'({"ac"[row]}) {title}: design',loc='left')
        right.set_title(f'({"bd"[row]}) {title}: loss',loc='left')
        design(left,report['studies']['mixed_'+loss]['diagnostics'],constant)
        for rule,color,marker in [(loss,blue,'o'),('bures' if loss=='frobenius' else 'frobenius',gray,'s')]:
            rows=report['studies']['mixed_'+rule]['risks']
            means=np.array([v['mean'][index] for v in rows])
            se=np.array([v['mc_se'][index] for v in rows])
            label='Algorithm 1 (Bures)' if rule=='bures' else 'Algorithm 2 (Frobenius)'
            right.errorbar(n,means,yerr=error_multiplier*se,color=color,marker=marker,
                           ms=3,capsize=2,lw=1,label=label)
        right.set_ylabel(r'$\widehat{R}_F(n)$' if loss=='frobenius' else r'$\widehat{R}_B(n)$')
        frame(right,n,constant,'upper right')
    fig.tight_layout(w_pad=1.5,h_pad=1.5)
    save(fig,'figure1_mixed')
    fig,(left,right)=plt.subplots(1,2,figsize=(7.1,3.15))
    fig.suptitle(r'Algorithm 3: pure state, $D=4$ (two qubits)',fontsize=11)
    left.set_title('(a) Squared Bures: mean design',loc='left')
    right.set_title('(b) Squared Bures: loss',loc='left')
    design_means = np.asarray([row['mean'] for row in design_summary['rows']])
    design_se = np.asarray([row['mc_se'] for row in design_summary['rows']])
    for j,color,marker,label in [
        (0,blue,'o',r'$\widehat C_n^{\rm cur}$: current design'),
        (1,orange,'s',r'$\widehat C_n^{\rm avg}$: accumulated information')]:
        left.plot(n,design_means[:,j],color=color,marker=marker,ms=3,lw=1.1,label=label)
        left.fill_between(n,design_means[:,j]-error_multiplier*design_se[:,j],
                          design_means[:,j]+error_multiplier*design_se[:,j],
                          color=color,alpha=.16,linewidth=0)
    gap = max(float(np.max(design_means+error_multiplier*design_se)-3),.075)
    left.set_ylim(3-gap*.12,3+gap*1.55)
    left.set_ylabel(r'Mean information criterion $\widehat C_n$')
    frame(left,n,3,'upper right')
    rows=report['studies']['pure_algorithm3']['risks']
    for method,color,marker,label in [(1,blue,'o','Corrected (Algorithm 3)'),(0,gray,'s','Uncorrected preliminary')]:
        means=np.array([v['mean'][method][1] for v in rows])
        se=np.array([v['mc_se'][method][1] for v in rows])
        right.errorbar(n,means,yerr=error_multiplier*se,color=color,marker=marker,
                       ms=3,capsize=2,lw=1,label=label)
    right.set_ylabel(r'$\widehat{R}_B(n)$')
    frame(right,n,3,'center right')
    fig.subplots_adjust(left=.095,right=.985,bottom=.20,top=.84,wspace=.30)
    save(fig,'figure2_pure_bures')
    dimensions=report['configuration']['optional_covariance_dimensions']
    if dimensions:
        fig,axes=plt.subplots(1,len(dimensions),figsize=(6.7,2.9),sharey=True,squeeze=False)
        handles=[]
        for ax,D in zip(axes[0],dimensions):
            study=report['studies'][f'optional_D{D}'];rows=study['risks']
            x=np.array([v['n'] for v in rows])
            for key,color,marker,label in [('uncorrected',gray,'s','Uncorrected preliminary'),('corrected',blue,'o','Tangent correction')]:
                h=ax.errorbar(x,[v[key]['mean_tangent_variance'] for v in rows],
                    yerr=[error_multiplier*v[key]['variance_mc_se'] for v in rows],
                    color=color,marker=marker,ms=3,capsize=2,lw=1,label=label)
                if ax is axes[0,0]:handles.append(h)
            line=ax.axhline(study['variance_target_uncorrected'],color='black',ls='--',lw=.9,label=r'Uncorrected limit $v_D$')
            bound=ax.axhline(1,color='black',ls=':',lw=1.1,label='Gill-Massar bound')
            if ax is axes[0,0]:handles.extend([line,bound])
            ax.set_xscale('log',base=2)
            ax.set_xticks(x,[fr'$2^{{{int(np.log2(v))}}}$' for v in x])
            ax.set_xlabel('Copies, $n$');ax.set_title(f'$D={D}$');ax.grid(axis='y',alpha=.15)
        axes[0,0].set_ylabel(r'Mean tangent variance $\widehat{V}_n$')
        fig.legend(handles,[h.get_label() for h in handles],loc='lower center',ncol=2,frameon=False,fontsize=9)
        fig.subplots_adjust(left=.10,right=.98,top=.9,bottom=.34,wspace=.18)
        save(fig,'figureS_covariance')
    metadata={'status':'PASS','replications':R,'new_simulation_run_by_plotter':False,
        'pure_design_panel':'Mean per-record criteria over all original pure loss replicates',
        'pure_design_means_and_MCSEs_recomputed':True,
        'pure_design_seed_selection':False,
        'source_design_samples_sha256':hashlib.sha256((results_directory/'pure_design_samples.npz').read_bytes()).hexdigest(),
        'source_design_summary_sha256':hashlib.sha256((results_directory/'pure_design_summary.json').read_bytes()).hexdigest(),
        'saved_primary_means_and_MCSEs_recomputed':True,
        'saved_optional_covariance_bias_loss_and_paired_diagnostics_recomputed':True,
        'Matplotlib':matplotlib.__version__,
        'source_results_sha256':hashlib.sha256((results_directory/'results.json').read_bytes()).hexdigest(),
        'files':{f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in output.glob('figure*') if f.suffix in ['.pdf','.png']}}
    (output/'figure_receipt.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))
