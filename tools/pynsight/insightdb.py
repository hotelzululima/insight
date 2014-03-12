import insight.debugger 
from insight.debugger import *
import argparse
import code

# change Python path to load modules from working directory 
sys.path += [ '.' ]
# change the prompt
sys.ps1 = "insightdb> "

banner = """Insight-based Debugger
Try help (insight.debugger) to get information on debugger commands.
"""

#
# command-line arguments
#
parser = argparse.ArgumentParser (prog="insighdb")
parser.add_argument ('-b', '--target', help='enforce BFD target', 
                     dest = "target", default = "", 
                     required = False, 
                     metavar ="bfd-target-name")

parser.add_argument ('inputfile', help='binary file', 
                     default = None, nargs = '?') 
                     

parser.add_argument ('-q', '--quiet', help='disable verbosity.', 
                     dest = "quiet", default = False, 
                     action = "store_true")
parser.add_argument ('-x', '--xml', help='preload an existing microcode in '
                     'XML format.', 
                     dest = "xmlmc", metavar="microcode", default = None)

#
# aliases for debugger commands
# 
f = insight.debugger.binfile
r = insight.debugger.run
ms = insight.debugger.microstep
s = insight.debugger.step
c = insight.debugger.cont
b = insight.debugger.breakpoint
watch = insight.debugger.watchpoint
d = insight.debugger.delete_breakpoints
P = insight.debugger.prog
pc = insight.debugger.pc
ep = insight.debugger.entrypoint
cond = insight.debugger.cond


if __name__ == "__main__":
    args = parser.parse_args()
    if not args.quiet:
        print banner
    if args.inputfile != None:
        binfile (args.inputfile, args.target)
        if args.xmlmc != None and P() != None:
            load_mc (args.xmlmc)
    try:
        from mydb import *
    except ImportError:
        pass
    code.interact ("", local = globals ())

