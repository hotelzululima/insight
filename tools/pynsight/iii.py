import insight.debugger
from insight.debugger import *
import argparse
import code
import importlib

# change Python path to load modules from working directory
sys.path += ['.']
# change the prompt
sys.ps1 = "iii> "

banner = """Insight Debugger
Try 'help(insight.debugger)' to get information on debugger commands.
Type 'aliases()' to display list of defined aliases.
"""


#
# command-line arguments
#
parser = argparse.ArgumentParser(prog="insighdb")
parser.add_argument('-b', '--target', help='enforce BFD target',
                    dest="target", default="",
                    required=False,
                    metavar="bfd-target-name")

parser.add_argument('-m', '--architecture', help='enforce BFD architecture',
                    dest="architecture", default="",
                    required=False,
                    metavar="bfd-architecture-name")

parser.add_argument('-c', '--init-module', help='initializaiton module',
                    dest="initmodule", default="iiirc",
                    required=False,
                    metavar="init-module")

parser.add_argument('inputfile', help='binary file',
                    default=None, nargs='?')


parser.add_argument('-q', '--quiet', help='disable verbosity.',
                    dest="quiet", default=False,
                    action="store_true")
parser.add_argument('-x', '--xml', help='preload an existing microcode in '
                    'XML format.',
                    dest="xmlmc", metavar="microcode", default=None)

#
# aliases for debugger commands
#
aliases_ = {'f': insight.debugger.binfile,
            'r': insight.debugger.run,
            'ms': insight.debugger.microstep,
            's': insight.debugger.step,
            'c': insight.debugger.cont,
            'b': insight.debugger.breakpoint,
            'w': insight.debugger.watchpoint,
            'd': insight.debugger.delete_breakpoints,
            'P': insight.debugger.prog,
            'pc': insight.debugger.pc,
            'ep': insight.debugger.entrypoint,
            'cond': insight.debugger.cond}

for a in aliases_.keys():
    globals()[a] = aliases_[a]


def aliases():
    """Display current aliases of insgith db"""
    for a in aliases_.keys():
        print "{:10s} -> {}".format(a, aliases_[a].__name__)

if __name__ == "__main__":
    args = parser.parse_args()
    if not args.quiet:
        print banner
    if args.inputfile is not None:
        binfile(args.inputfile, "symbolic", args.target, args.architecture)
        if args.xmlmc is not None and P() is not None:
            load_mc(args.xmlmc)

    try:
        m = importlib.import_module(args.initmodule)
        globals().update(m.__dict__)
    except ImportError, e:
        print e
    except IOError, e:
        print e
    code.interact("", local=globals())
