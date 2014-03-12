import insight.debugger 
from insight.debugger import *

#
# Aliases
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

def main ():
    print "Insight Debugger"
    print "Try help(insight.debugger) to get information on debugger commands."
    print

    if len (sys.argv) == 2:
        binfile (sys.argv[1])
    elif len (sys.argv) == 3:
        binfile (sys.argv[1],sys.argv[2])


if __name__ == "__main__":
    main ()
    try:
        from mydb import *
    except ImportError:
        pass
