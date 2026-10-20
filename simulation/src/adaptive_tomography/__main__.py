"""Command-line entry point; all paths are portable and caller-selected."""
import argparse
import json
from pathlib import Path
from .simulation import run


def main():
    parser=argparse.ArgumentParser(description='Adaptive quantum tomography: paper reproduction')
    sub=parser.add_subparsers(dest='command',required=True)
    sim=sub.add_parser('run',help='Run all configured simulations from the Born observation law')
    sim.add_argument('--config',type=Path,default=Path('configs/paper.json'))
    sim.add_argument('--output',type=Path,default=Path('results/paper'))
    sim.add_argument('--replications',type=int)
    sim.add_argument('--max-power',type=int)
    plot=sub.add_parser('plot',help='Render the paper figures from saved replicate data')
    plot.add_argument('--results',type=Path,default=Path('results/paper'))
    plot.add_argument('--output',type=Path,default=Path('figures'))
    design=sub.add_parser('design',help='Replay every pure loss record and save averaged information criteria')
    design.add_argument('--results',type=Path,default=Path('results/paper'))
    args=parser.parse_args()
    if args.command=='run':
        config=json.loads(args.config.read_text())
        if args.replications is not None:config['replications']=args.replications
        if args.max_power is not None:
            config['main_batch_schedule']['maximum']=2**args.max_power
            config['optional_maximum_reporting_power']=args.max_power
        run(config,args.output)
    elif args.command=='design':
        from .design import replay_pure_design
        replay_pure_design(args.results)
    else:
        from .plotting import render
        render(args.results,args.output)


if __name__=='__main__':main()
