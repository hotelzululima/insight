import sys
import insight
from insight.utils import *

program = None
simulator = None
prompt = "pynsight:{}> "
sys.ps1 = "pynsight:> "

def file(filename,target=""):
    """Load a binary file.

    This function loads from 'filename' a binary program into memory. If a BFD 
    target name has been specified then it is passed to Insight loader.

    On success currently loaded program and running simulator are cleared. The 
    program is set to the new one and the simulator is set to None. 

    Command-line prompt is modified to indicate currently loaded binary.
    """
    global program
    program = insight.io.load_bfd (filename, target)
    simulator = None
    sys.ps1 = prompt.format (filename)
    
def run():
    global simulator, program
    if simulator != None:
        for a in simulator.run ():
            print a
        return
    if program == None:
        if len (sys.argv) == 2:
            file (sys.argv[1])
        elif len (sys.argv) == 3:
            file (sys.argv[1],sys.argv[2])
    if program == None:
        raise RuntimeWarning, "No program has been loaded"

    insight.config.set ("kernel.expr.solver.name", "mathsat")
    simulator = program.simulator ()
    simulator.run ()
    arrows ()

def arrows():
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    i = 0
    for a in simulator.get_arrows():
        print i, ":", a
        i += 1

def simulation_error ():
    global simulator
    if sys.exc_type is insight.error.UndefinedValueError:
        print "execution interrupted:"
        print sys.exc_value
    elif sys.exc_type is insight.error.BreakpointReached:
        (id, (ga,la)) = sys.exc_value
        print "breakpoint {} reached at (0x{:x}, {})".format (id, ga, la)
    elif sys.exc_type is insight.error.SinkNodeReached:
        (ga,la) = sys.exc_value
        print "sink node reached after (0x{:x}, {})".format(ga,la)
    elif sys.exc_type is insight.error.JumpToInvalidAddress:
        (ga,la) = sys.exc_value
        print "try to jump into undefined memory (0x{:x}, {})".format(ga,la)
    elif sys.exc_type is insight.error.NotDeterministicBehaviorError:
        print "stop in a configuration wtih several output arrows"
    else:
        raise 

def microstep(a = 0):
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    try:
        simulator.microstep (a)
    except:
        simulation_error ()
    arrows ()

def step():
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    try:
        simulator.step ()
    except:
        simulation_error ()
    arrows ()

def cont():
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    try:
        while True:
            simulator.step ()
    except:
        simulation_error ()
    arrows ()

def dump(addr = None, l = 256):
    global program, simulator
    
    if addr == None:
        if simulator == None:
            print "Program is not started. Dump from entrypoint"
            addr = program.info()["entrypoint"]
        else:
            addr = simulator.get_pc()[0]
    if simulator == None:
        pretty_print_memory (program, addr, l)
    else:
        for v in simulator.get_memory (addr, l):
            print v

def disas(l=20):
    global program, simulator
    if simulator == None:
        print "Program is not started. Disas from entrypoint"
        addr = program.info()["entrypoint"]
    else:
        addr = simulator.get_pc()[0]
    for inst in program.disas (addr, l):
        print "0x{:x} : {}".format (inst[0],inst[1])

def breakpoint(g=None,l=0):
    global simulator,program

    if g == None:
        if simulator == None:
            print "Program is not started; set breakpoint to entrypoint."
            g = program.info()["entrypoint"]
            l = 0
        else:
            g = simulator.get_pc()[0]
            l = simulator.get_pc()[1]
    bp = simulator.add_breakpoint (g,l)
    if bp != None:
        print "breakpoint already set at (0x{:x},{}) with id ({}).".format (bp[1][0], bp[1][1], bp[0])

def delete_breakpoints(l=None):
    global simulator
    if simulator == None:
        return
    if isinstance (l,int):
        l = [ l ]
    if l == None:
        l=[]
        for (id,a) in simulator.get_breakpoints ():
            l = l + [ id ]
    for bp in l:
        if not simulator.del_breakpoint (bp):
            print "unknown breakpoint", bp

def info (what):
    global program, simulator
    if "breakpoints".find (what) == 0 and simulator != None:
        for (id, (ga,la)) in simulator.get_breakpoints ():
            print id, " : (0x{:x},{})".format (ga,la)
    elif "entrypoint".find (what) == 0 or "ep".find (what) == 0:
        print "0x{:x}".format (entrypoint()[0], entrypoint()[1])
    elif "pc".find (what) == 0:
        print "0x{:x}".format (pc()[0], pc()[1])

def pc():
    global simulator
    if simulator == None:
        print "Program is not started."
        return None
    return simulator.get_pc ()

def entrypoint():
    global simulator
    if simulator == None:
        print "Program is not started."
        return None
    return simulator.get_pc ()

def symbols():
    global program
    for (s,a) in program.symbols ():
        print "0x{:x} : {}".format (a, s)

def registers(l=None):
    global simulator
    if simulator == None:
        print "Program is not started."
        return
    if isinstance (l, str):
        l = [l]
    regs = program.info()["registers"];
    for r in l:
        if r in regs:
            fmt = "{: <5s} : {}"
            val = simulator.get_register (r)
            if val != None:
                print fmt.format (r, simulator.get_register (r))
    
def prog(): 
    global program
    return program

def set(loc, val):
    global simulator
    if simulator == None:
        print "program is not started"
        return
    if isinstance (loc, str):
        regs = prog().info()["registers"]
        if loc in regs:
            simulator.set_register (loc, val)
        else:
            print "unknown register ", loc
    elif isinstance (val, int):
        simulator.set_memory (loc, 0xFF & val)
    else:
        for b in val:
            simulator.set_memory (loc, 0xFF & b)
            loc += 1
