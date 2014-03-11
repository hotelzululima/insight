import sys
import insight
from insight.utils import *

program = None
simulator = None
prompt = "pynsight:{}> "
sys.ps1 = "pynsight:> "
hooks = {}
sys.path += [ '.' ]

def binfile(filename,target=""):
    """Load a binary file.

    This function loads from 'filename' a binary program into memory. If a BFD 
    target name has been specified then it is passed to Insight loader.

    On success currently loaded program and running simulator are cleared. The 
    program is set to the new one and the simulator is set to None. 

    Command-line prompt is modified to indicate currently loaded binary.
    """
    global program
    try:
        program = insight.io.load_bfd (filename, target)
        simulator = None
        sys.ps1 = prompt.format (filename)
    except insight.error.BFDError, e:
        print e

def exec_hooks (f):
    global hooks
    if f in hooks:
        for h in hooks[f]:
            h ()

def add_hook (f, h):
    if f in hooks:
        hooks[f] += [h]
    else:
        hooks[f] = [h]

def add_run_hook (h): add_hook (run, h)
def add_step_hook (h): add_hook (step, h)
def add_cont_hook (h): add_hook (cont, h)
def add_microstep_hook (h): add_hook (microstep, h)

def run(ep=None, dom="symbolic"):
    """Start simulation"""
    global simulator, program
    if simulator != None:
        simulator.run ()
        if ep != None and ep != pc()[0]:
            simulator = program.simulator (start=ep, domain=dom)
            simulator.run ()
        exec_hooks (run)
        arrows ()
        return
    if program == None:
        if len (sys.argv) == 2:
            binfile (sys.argv[1])
        elif len (sys.argv) == 3:
            binfile (sys.argv[1],sys.argv[2])
    if program == None:
        return

    insight.config.set ("kernel.expr.solver.name", "mathsat")
    if ep == None:
        ep = entrypoint ()
    simulator = program.simulator (start=ep, domain=dom)
    simulator.run ()
    exec_hooks (run)
    arrows ()

def arrows():
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    i = 0
    print "Arrows from (0x{:x},{}):".format (pc()[0],pc()[1])
    for a in simulator.get_arrows():
        print i, ":", a
        i += 1

def simulation_error ():
    global simulator
    if sys.exc_type is insight.error.UndefinedValueError:
        print "execution interrupted:"
        print sys.exc_value
    elif sys.exc_type is insight.error.BreakpointReached:
        (id, s) = sys.exc_value
        print "stop condition {} reached: {}".format (id, s)
    elif sys.exc_type is insight.error.SinkNodeReached:
        (ga,la) = sys.exc_value
        print "sink node reached after (0x{:x}, {})".format(ga,la)
    elif sys.exc_type is insight.error.JumpToInvalidAddress:
        (ga,la) = sys.exc_value
        print "try to jump into undefined memory (0x{:x}, {})".format(ga,la)
    elif sys.exc_type is insight.error.NotDeterministicBehaviorError:
        print "stop in a configuration with several output arrows"
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
    exec_hooks (microstep)
    arrows ()

def step(a = 0):
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    try:
        simulator.step (a)        
    except:
        simulation_error ()
    exec_hooks (step)
    arrows ()

def cont(a = 0):
    global simulator
    if simulator == None:
        print "Program is not started"
        return
    try:
        simulator.step (a)
        while True:
            simulator.step ()
    except:
        simulation_error ()
    exec_hooks (cont)
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

def disas(addr = None, l=20, labels=True, bytes=False, holes=False):
    global program, simulator
    if simulator == None:
        print "Program is not started. Disas from entrypoint"
        if addr == None:
            addr = program.info()["entrypoint"]
        for inst in program.disas (addr, l):
            print "0x{:x} : {}".format (inst[0],inst[1])
    else:
        if addr != None:
            simulator.get_microcode().asm (addr, l, bytes, holes, labels)
        else:
            simulator.get_microcode().asmall (bytes, holes, labels)

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
        print "breakpoint already set at (0x{:x},{}) with id ({}).".format (g, l, bp[0])

def cond (id, e = None):
    global simulator

    if simulator == None:
        print "Program is not started; set breakpoint to entrypoint."
        return None;
    bp = None
    if e == None:
        bp = simulator.set_cond (id)        
    elif isinstance (e, str):
        bp = simulator.set_cond (id, e)
    else:
        raise TypeError, e
    if bp == None:
        print "no such breakpoint ", id
        return
    elif e == None:
        print "making breakpoint", id," unconditional"
    else:
        print "making breakpoint", id," conditional"
    print bp[0], " : ", bp[1]

def watchpoint(cond):
    global simulator
    if simulator == None:
        print "Program is not started"
        return 
    bp = simulator.add_watchpoint (cond)
    if bp != None:
        print "watchpoint already setid ({}).".format (bp[0])

def pywatchpoint (cb):
    global simulator
    if simulator == None:
        print "Program is not started"
        return 
    if cb == None :
        print "Invalid argument", cb, " is not a callable object"
        return

    bp = simulator.add_pywatchpoint (cb)
    if bp != None:
        print "watchpoint already setid ({}).".format (bp[0])

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
        for (id, s) in simulator.get_breakpoints ():
            print id, " : {}".format (s)
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
    global program
    if program == None:
        print "no program is loaded"
        return None
    return program.info()["entrypoint"]

def print_symbols():
    global program
    for (s,a) in program.symbols ():
        print "0x{:x} : {}".format (a, s)

def print_registers(l=None):
    """Display values of registers specified in l.

    For each name of register given in iterable object 'l', the function 
    displays its value according to the current context of the simulation. If
    no value has been assigned yet to a register this latter is not displayed.

    If 'l' is 'None' then all registers are considered.
    """
    global simulator
    if simulator == None:
        print "Program is not started."
        return 
    if l == None:
        l = program.info()["registers"].keys()
    if isinstance (l, str):
        l = [l]
    regs = program.info()["registers"];
    
    for r in sorted (l):
        if r in regs:
            fmt = "{: <5s} : {}"
            val = simulator.get_register (r)
            if val != None:
                print fmt.format (r, simulator.get_register (r))

def register(regname):
    """Returns the value of a register."""
    global simulator
    if simulator == None:
        print "Program is not started."
        return
    try:
        return simulator.get_register (regname)
    except LookupError, e:
        print e, regname
    
def prog(): 
    """Returns the program being debugged."""
    global program
    return program

def set(loc, val = None):
    """Assign a value to register or a location in memory.
    """
    global simulator
    if simulator == None:
        print "program is not started"
        return
    try:
        if isinstance (loc, str):
            regs = prog().info()["registers"]
            if loc in regs:
                if val == None:
                    simulator.concretize_register (loc)
                else:
                    simulator.set_register (loc, val)
            else:
                print "unknown register ", loc
        elif val == None:
            simulator.concretize_memory (loc)
        elif isinstance (val, int):
            simulator.set_memory (loc, 0xFF & val)
        else:
            for b in val:
                simulator.set_memory (loc, 0xFF & b)
                loc += 1
    except insight.error.ConcretizationException:
        print "try to assign an inconsistent value to", loc

def unset(loc, len = 1, keep = True):
    """Abstract the value of a register or a memory area."""
    global simulator
    if simulator == None:
        print "program is not started"
        return
    try:
        if isinstance (loc, str):
            regs = prog().info()["registers"]
            if loc in regs:
                simulator.unset_register (loc, keep)
            else:
                print "unknown register ", loc
        else:
            simulator.unset_memory (loc, len, keep)
    except NotImplementedError:
        print "abstraction is not supported here."

def instr(addr=None):
    """Assembler instruction at address 'addr'.

    This method displays the assembler instruction located at 'addr'. If the
    parameter is omitted or is 'None' the program counter of the current 
    simulation is used. Note that this method directly uses Insight's decoder; 
    no access to currently built MC is done."""
    global program
    if program == None:
        print "no program is loaded"
    if addr == None:
        disas(l=1)
    else:
        for i in program.disas (addr, 1):
            print i[1]

def print_state():
    global simulator
    if simulator == None:
        print "program is not started"
        return 
    print simulator.state ()

