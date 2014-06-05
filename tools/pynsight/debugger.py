import sys
import insight
import xdot
from insight.utils import *

program = None
simulator = None
hooks = {}
startpoint = None
dotviewer = None
recorder = None
displayed_expressions = []

insight.config.set("kernel.expr.solver.name", "mathsat")


def binfile(filename, domain="symbolic", target="", architecture=""):
    """
    Load a binary file.

    This function loads from 'filename' a binary program into memory. If a
    BFD 'target' name has been specified then it is passed to Insight loa-
    der. Parameter 'domain' specifies the interpretation domain used by the
    simulator.

    On success, currently loaded program and running simulator are cleared.
    The program is set to the new one and a new simulator is started.

    Parameters:
    - filename : name of the file containing bytes to read.
    - domain   : the interpretation domain used by the simulator. It can be
                 'symbolic' or 'concrete'
    - target   : name of a BFD target supported by Insight (e.g elf32-i386).
    - architecture : name of a BFD architecture supported by Insight
    """
    global program, simulator, startpoint
    try:
        program = insight.io.load_bfd(filename, target, architecture)
        simulator = program.simulator(domain)
        startpoint = entrypoint()
    except insight.error.BFDError, e:
        print e


def exec_hooks(f):
    """
    Run hooks for the specified debugger function 'f'

    The simulator allows to attach callbacks to simulation function (run,
    microstep, step, cont). These callbacks are called juste after the
    execution of the corresponding function.

    See add_hook, add_run_hook, add_step_hook, add_microstep_hook and
    add_cont_hook.

    Parameters:
    - f : the reference to the simulation function with hooks.
    """
    global hooks
    if f in hooks:
        for h in hooks[f]:
            h()


def add_hook(f, h):
    """
    Attach a hook the simulation function 'f'.

    To be effective 'f' must be a function used by simulation i.e. run,
    step, cont or microstep. Hooks are executed in the order they are intro-
    duced. A same hook can be added several times.

    Parameters:
    - f : the reference to the simulation function to be hooked.
    - h : the hook callback
    """
    if f in hooks:
        hooks[f] += [h]
    else:
        hooks[f] = [h]


def del_hook(f, hindex):
    """
    Remove a hook attached to the simulation function 'f'.

    Parameters:
    - f : the reference to the simulation function to be hooked.
    - h : the index of the hook callback as given by 'show("hooks")'
    """
    if f in hooks:
        hlist = hooks[f]
        if not (0 <= hindex and hindex < len(hooks[f])):
            print "invalid argument; index should be in range [0, {:d}]."\
                .format(len(hooks[f]))
        else:
            hlist[hindex:hindex+1] = []
    else:
        print "no hook is attached to", f.__name__


def add_run_hook(h):
    """
    Add a hook to 'run' function.

    Parameters:
    - h : the hook callback attached to 'run' function.
    """
    add_hook(run, h)


def del_run_hook(hindex):
    """
    Remove a hook attached to 'run' function.

    Parameters:
    - hindex : index of the hook given by 'show ("hooks")'.
    """
    del_hook(run, hindex)


def add_step_hook(h):
    """
    Add a hook to 'step' function.

    Parameters:
    - h : the hook callback attached to 'step' function.
    """
    add_hook(step, h)


def del_step_hook(hindex):
    """
    Remove a hook attached to 'step' function.

    Parameters:
    - hindex : index of the hook given by 'show ("hooks")'.
    """
    del_hook(step, hindex)


def add_cont_hook(h):
    """
    Add a hook to 'cont' function.

    Parameters:
    - h : the hook callback attached to 'cont' function."""
    add_hook(cont, h)


def del_cont_hook(hindex):
    """
    Remove a hook attached to 'cont' function.

    Parameters:
    - hindex : index of the hook given by 'show ("hooks")'.
    """
    del_hook(cont, hindex)


def add_microstep_hook(h):
    """
    Add a hook to 'microstep' function.

    Parameters:
    - h : the hook callback attached to 'microstep' function."""
    add_hook(microstep, h)


def del_microstep_hook(hindex):
    """
    Remove a hook attached to 'microstep' function.

    Parameters:
    - hindex : index of the hook given by 'show ("hooks")'.
    """
    del_hook(microstep, hindex)


def run(ep=None):
    """
    Start/restart simulation.

    If no startpoint 'ep' is specified then simulation is started from the
    last one (which is set to the entrypoint of the program if it is the
    first call to 'run').

    Hooks for 'run' method are called just after the initialization of the
    simulation. Then, the list of enabled arrows is displayed.

    Parameters:
    - ep : the entrypoint of the simulation.
    """
    global simulator, program, startpoint, recorder
    if program is None:
        print "no program is loaded"
        return

    if ep is None:
        ep = startpoint

    __record(ep, run, ep, True)
    simulator.run(ep)
    startpoint = ep
    exec_hooks(run)
    arrows()


def arrows():
    """
    Display enabled arrows.

    Print the list of arrows that lead into a new state. Arrows with a
    falsified guard or with an invalid target are not displayed.

    Arrows are numbered; these numbers are passed to simulation methods to
    specify the next arrow to follow.
    """
    global simulator
    if simulator is None:
        print "Program is not started"
        return
    try:
        i = 0
        print "Arrows from (0x{:x},{}):".format(mcpc()[0], mcpc()[1])
        for a in simulator.get_arrows():
            print i, ":", a
            i += 1
    except:
        simulation_error()


def microstep(a=0):
    """
    Execute an arrow of the microcode.

    Parameters:
    - a : indicates the index of an arrow in the list of enabled ones (see
          'help(arrows)').
    """
    global simulator, recorder
    if simulator is None:
        print "Program is not started"
        return
    __record(pc(), microstep, a)
    try:
        simulator.microstep(a)
    except:
        simulation_error()
    exec_hooks(microstep)
    arrows()


def step(a=0):
    """
    Execute an assembler instruction.

    'a' is used in the case where several arrows are enabled in the current
    state. In this case 'a' is the index of the first arrow that is execu-
    ted. All micro-steps of the instruction are executed unless a choice is
    required.

    Hooks are triggered after the execution of the instruction (even it is
    not completed).

    Parameters:
    - a : the index of an enabled arrow.
    """

    global simulator, recorder
    if simulator is None:
        print "Program is not started"
        return
    __record(pc(), step, a)
    try:
        simulator.step(a)
    except:
        simulation_error()
    exec_hooks(step)
    arrows()


def cont(a=0, show_arrows=True):
    """
    Continue simulation of the program.

    The simulation is continued until a choice point is encountered. Actual-
    ly 'step' function is iterated until a simulation exception is raised.

    If in the current state several arrows are enabled then 'a' is the index
    of the arrow used as the first micro-step.

    Hooks are triggered when the simulation stop.

    Parameters:
    - a : the index of an enabled arrow.
    """
    global simulator, recorder
    if simulator is None:
        print "Program is not started"
        return
    __record(pc(), cont, a)
    try:
        simulator.step(a)
        while True:
            simulator.step()
    except:
        simulation_error()
    exec_hooks(cont)
    if show_arrows:
        arrows()


def dump(addr=None, l=256, filter=None):
    """
    Display content of memory.

    This function prints the content of memory in the current state. Output
    depends on the interpretation domain. In order to dump bytes of the
    loaded binary file you must use 'utils.pretty_print_memory'.

    Parameters:
    - addr   : start address of the dumped memory area. If 'addr' is not
               specified then the value of the program-counter is used (see
               'help(pc)').
    - l      : the number of bytes to display.
    - filter : a callback to translate domain-specific string into another
               value.
    """
    global simulator

    if simulator is None:
        print "Program is not started."
        return
    try:
        if addr is None:
            addr = pc()
        for v in simulator.get_memory(addr, l):
            if filter is not None:
                v = filter (v)
            print v
    except:
        simulation_error()


def disas(addr=None, l=20, labels=True, bytes=False, holes=False):
    """
    Disassemble memory.

    This function prints instructions that annotates the microcode. In order
    to get instructions directly from the binary file under study you should
    use 'utils.pretty_disas_memory' instead.

    Only instruction discovered up to the current state of simulation are
    printed; more can be displayed in the case of a pre-loaded microcode
    (see 'help (load_mc)').

    Parameters:
    - addr   : address of the first instruction
    - l      : the number of instructions to display
    - labels : display labels of jump targets; if no symbol exists for a
               target then a random one is generated (not stored in symbol
               table).
    - bytes  : display raw bytes of the instruction
    - holes  : if some bytes are not decoded between two instructions then
               they are printed in a raw way.
    """
    global simulator
    if simulator is None:
        print "Program is not started."
        return
    if addr is not None:
        simulator.get_microcode().asm(addr, l, bytes, holes, labels)
    else:
        simulator.get_microcode().asmall(bytes, holes, labels)


def breakpoint(g=None, l=0):
    """
    Add a breakpoint.

    This function attaches a breakpoint at a given microcode address. For
    convenience local part of the microcode address is set to 0 by default.
    Each time the simulator encounter the specified address it stops.

    Breakpoints are attached to a simulator i.e. if a new binary file is
    loaded existing breakpoints are lost.

    The list of created breakpoints can be obtain using the function 'show'.

    Parameters:
    - g : the global address of the breakpoint. If not specified the value
          of the program counter is used.
    - l : a local address for microcode addresses.
    """
    global simulator

    if simulator is None:
        print "Program is not started."

    try:
        if g is None:
            g = simulator.get_pc()[0]
            l = simulator.get_pc()[1]
        bp = simulator.add_breakpoint(g, l)
        print "breakpoint set at (0x{:x},{}) with id={}.".format(g, l, bp[0])
        return bp[0]
    except:
        simulation_error()
    return None

def cond(id, e=None):
    """
    Attach a condition to a breakpoint.

    By default simulator stops when it encounters a breakpoint. A condition
    to stop can be attached to each breakpoint. The expression is evaluated
    after each microstep. If the condition cannot be evaluated or is evalua-
    ted to a 'true' value then the simulation stops.

    If no condition 'e' is specified then the existing condition is removed.

    Parameters:
    - id : the identifier of a breakpoint (see 'show ("breakpoints")').
    - e : a string containing a expression respecting Insight syntax.
    """
    global simulator

    if simulator is None:
        print "Program is not started; set breakpoint to entrypoint."
        return None
    bp = None
    if e is None or isinstance(e, str):
        bp = simulator.set_cond(id, e)
    else:
        raise TypeError(e)
    if bp is None:
        print "no such breakpoint ", id
        return
    elif e is None:
        print "making breakpoint", id, " unconditional"
    else:
        print "making breakpoint", id, " conditional"
    print bp[0], " : ", bp[1]


def watchpoint(cond):
    """
    Create a watchpoint.

    A watchpoint observes the value of some condition. The simulator stops
    each time the value of the watchpoint change. The condition must respect
    the syntax of Insight expressions.

    Current active watchpoints appear in the list of breakpoints given by
    'show("breakpoints")'.

    Parameters:
    - cond : an Boolean expression respecting Insight syntax
    """
    global simulator
    if simulator is None:
        print "Program is not started"
        return
    bp = simulator.add_watchpoint(cond)
    if bp is not None:
        print "watchpoint already setid({}).".format(bp[0])


def pywatchpoint(cb):
    """
    Create a Python watchpoint.

    Python watchpoints are similar to watchpoints (see help('watchpoint')).
    In the case of watchpoints, the value of a condition is observed. The
    case of Python watchpoint a callback returning a Boolean is called at
    each microstep. If the callback returns a value different of 'None', the
    simulation is stopped.

    Current active Python watchpoints appear in the list of breakpoints
    given by 'show("breakpoints")'.

    Parameters:
    - cb : a reference to a function taht takes no argument and that returns
           a Boolean.
    """
    global simulator
    if simulator is None:
        print "Program is not started"
        return
    if cb is None:
        print "Invalid argument", cb, " is not a callable object"
        return

    bp = simulator.add_pywatchpoint(cb)
    if bp is not None:
        print "Python watchpoint already setid({}).".format(bp[0])


def delete_breakpoints(l=None):
    """
    Remove breakpoints.

    The function deletes specified stop-points from the simulator. 'l' is
    a list of identifiers (or only one identifier) of breakpoints, watch-
    points or Python watchpoints.

    If 'l' is 'None' then all breakpoints are deleted.

    Parameters:
    - l : a list of identifiers or a single identifier.
    """
    global simulator
    if simulator is None:
        return
    if isinstance(l, int):
        l = [l]
    if l is None:
        l = []
        for(id, a) in simulator.get_breakpoints():
            l = l + [id]
    for bp in l:
        if not simulator.del_breakpoint(bp):
            print "unknown breakpoint", bp


def show(what):
    """
    Display informations related to simulation.

    According to the 'what' parameter the following data are printed :
    - "breakpoints" : display the current breakpoints, watchpoints and
                      Python watchpoints
    - "pc" : display the value of the program counter.
    - "mcpc" : display the microcode address of the current microcode-node.
    - "hooks" : display hooks attached to simulation functions.

    A prefix of the keyword is enough.

    Parameters:
    - what : what kind of data to display.
    """
    global program, simulator
    try:
        if "breakpoints".find(what) == 0 and simulator is not None:
            for(id, h, s) in simulator.get_breakpoints():
                print id, " : hits={} {}".format(h, s)
        elif "assumptions".find(what) == 0 and simulator is not None:
            for(g, l, expr) in simulator.get_assumptions():
                if l == 0:
                    print "0x{:x} : {}".format(g, expr)
                else:
                    print "(0x{:x},{}) : {}".format(g, l, expr)
        elif "pc".find(what) == 0:
            print "0x{:x}".format(pc())
        elif "mppc".find(what) == 0:
            print "0x{:x}".format(mppc())
        elif "hooks".find(what) == 0:
            for hf in sorted(hooks.keys()):
                print "hooks for function", hf.__name__
                index = 0
                for h in hooks[hf]:
                    if h.__name__ is not None:
                        if h.__name__.find("__") == 0: # internal hook
                            continue
                        desc = h.__name__
                    else:
                        desc = str(h)
                    print "{:2d} : {}".format(index, desc)
                    index += 1
                if index == 0:
                    print "there is no hook"
    except:
        simulation_error()


def pc():
    """
    Returns the value of the program counter.
    """
    global simulator
    if simulator is None:
        print "Program is not started."
        return None
    return mcpc()[0]


def mcpc():
    """
    Returns the address of the current microcode-node.
    """
    global simulator
    if simulator is None:
        print "Program is not started."
        return None
    return simulator.get_pc()


def entrypoint():
    """
    Returns the entrypoint of the loaded program.
    """
    global program
    if program is None:
        print "no program is loaded"
        return None
    return program.info()["entrypoint"]


def print_symbols():
    """
    Print the symbol table.

    Display the content of the symbol table.
    """

    global program
    if program is None:
        print "no program is loaded"
        return
    for(s, a) in program.symbols():
        print "0x{:x} : {}".format(a, s)


def print_registers(l=None):
    """
    Display values of registers specified in l.

    For each name of register given in iterable object 'l', the function
    displays its value according to the current context of the simulation.
    If no value has been assigned yet to a register this latter is not dis-
    played. 'l' may be a single identifier.

    If 'l' is 'None' then all registers are displayed.

    Parameters:
    - l : the list of registers or a single identifier.
    """
    global simulator
    valuewidth = 60
    if simulator is None:
        print "Program is not started."
        return
    if l is None:
        l = program.info()["registers"].keys()
    if isinstance(l, str):
        l = [l]
    regs = program.info()["registers"]
    try:
        for r in sorted(l):
            if r not in regs:
                continue
            fmt = "{: <5s} : {:."+ str(valuewidth) + "s}"
            val = simulator.get_register(r)
            if val is not None:
                if len(val) >= valuewidth:
                    fmt += "..."
                print fmt.format(r, simulator.get_register(r))
    except:
        simulation_error()


def register(regname):
    """
    Returns the value of a register.

    The function returns the value of the specified register in the current
    state. If the register is not assigned then None is returned else a
    string representation of the value is returned. The result depends on
    the current interpretation domain.

    Parameters:
    - regname : the identifier of the register.
    """
    global simulator
    if simulator is None:
        print "Program is not started."
        return
    try:
        return simulator.get_register(regname)
    except LookupError, e:
        print e, regname
    except:
        simulation_error()


def prog():
    """
    Returns the program being debugged.

    An opaque object is created when a binary file is loaded.
    Try 'help(prog ())' to get related informations.
    """
    global program
    return program


def set(loc, val=None):
    """
    Assign a value to a register or a location in memory.

    If 'loc' is an integer value then it is considered as the address of a
    byte to assign; else, if 'loc' is a string, it is considered as a regis-
    ter name. If the specified value 'val' is None then the simulator choose
    the value to be assigned by itself.

    In order to maintain the consistency of the simulation, values assigned
    to registers or memory cells must be coherent with the current value (if
    any) of the assigned location. For instance if a register is already
    assigned a concrete value then it can not be assigned a different value.

    Parameters:
    - loc : the assigned variable.
    - val : the value to assign to 'loc'. This value must be an integer.
    """
    global simulator
    if simulator is None:
        print "program is not started"
        return
    try:
        if isinstance(loc, str):
            regs = prog().info()["registers"]
            if loc in regs:
                if val is None:
                    if simulator.concretize_register(loc) is None:
                        print """
can not choose a value in not-assigned register '{}'; choose a value by
yourself.\n""".format(loc)
                else:
                    simulator.set_register(loc, val)
            else:
                print "unknown register ", loc
        elif val is None:
            if simulator.concretize_memory(loc) is None:
                print "can not choose a value in a not-assigned memory cell\n"
        elif isinstance(val, int):
            simulator.set_memory(loc, 0xFF & val)
        else:
            for b in val:
                simulator.set_memory(loc, 0xFF & b)
                loc += 1
    except insight.error.ConcretizationException:
        print "try to assign an inconsistent value to", loc
    except:
        simulation_error()


def unset(loc, len=1, keep=True):
    """
    Abstract the value of a register or a memory area.

    This function replaces the current assignment of a location (memory cell
    or register) by an abstration of this value. This re-assignment depends
    on the interpretation domain.

    If a memory area is abstracted the 'len' parameter indicates its size.

    The simulator can track these abstraction by integrating it in its
    context. In this case later assignments of the same location would be
    consistent with the abstraction.

    If the interpretation domain does not support this operation a message
    is displayed.

    Parameters:
    - loc : the location to abstract. It is either an address (i.e. an
            integer value or a string to specify a register name.
    - len : the number of bytes of abstract (only for memory areas)
    - keep : to memorize the abstraction into the context.
    """
    global simulator
    if simulator is None:
        print "program is not started"
        return
    try:
        if isinstance(loc, str):
            if loc in prog().info()["registers"]:
                simulator.unset_register(loc, keep)
            else:
                print "unknown register ", loc
        else:
            simulator.unset_memory(loc, len, keep)
    except:
        simulation_error()


def instr(addr=None):
    """
    Assembler instruction at address 'addr'.

    This method displays the assembler instruction located at 'addr'. If the
    parameter is omitted or is 'None' the program counter of the current
    simulation is used.

    Parameters:
    - addr : address of the instruction."""
    global simulator

    if simulator is None:
        print "Program is not started."
        return
    try:
        if addr is None:
            addr = pc()

        instr = simulator.get_instruction(addr)
        if instr is None:
            for i in program.disas(addr, 1):
                instr = i[1]
                print instr
        else:
            print instr
    except:
        simulation_error()


def print_state():
    """
    Displays the current state of the simulation.

    The output depends on the interpretation domain.
    """
    global simulator
    if simulator is None:
        print "program is not started"
        return
    print simulator.state()


def info(k=None):
    """
    Display informations related to loaded program.

    The functions prints the data assiociated with the keyword 'k'. If no
    keyword is given then all data are displayed.

    Parameters:
    - k : the data to be displayed.
    """
    global program
    if program is None:
        print "no program is loaded"
        return
    infos = program.info()
    if k is None:
        for k in infos.keys():
            val = infos[k]
            if isinstance(val, int):
                print "{:20} : 0x{:x}({})".format(k, val, val)
            else:
                print "{:20} : {}".format(k, val)
    elif k in infos:
        print "{:20} : {}".format(k, infos[k])
    else:
        print "no such entry"


def save_mc(filename):
    """
    Save current Microcode into a file.

    The function stores into 'filename' the microcode rebuilt by the simula-
    tion. The saved microcode can be reloaded using 'load_mc'.

    Parameters:
    - filename : name of the output file.
    """
    global simulator
    if simulator is None:
        print "program is not started"
    else:
        simulator.save_mc(filename)


def load_mc(filename):
    """
    Load a microcode from an XML file.

    Each simulator is started with an empty microcode assocaited to it.
    This function permits to reload an existing microcode into the current
    simulator.

    Note that reloaded microcode must be coherent with current program.
    """
    global simulator
    if simulator is None:
        print "program is not started"
    else:
        simulator.load_mc(filename)

def load_stub(filename, addr, fold = False):
    """
    Load a microcode program at a given address.

    This function loads an existing program from file 'filename' and reloca-
    tes it at the given address 'addr'. The loaded program is merged within
    the existing microcode; each node is relocated by shifting its location
    with 'addr' bytes.

    Take care that loaded stubs don't overlap existing nodes. In this case
    both microcodes exist.

    Parameters:
    - filename : input filename
    - addr     : offset where the microcode is relocated
    - fold     : whether the stub should be folded into one global address
    """
    global simulator
    if simulator is None:
        print "program is not started"
    else:
        simulator.load_stub(filename, addr, fold)


def simulation_error():
    """Internal function"""
    global simulator
    if sys.exc_type is insight.error.UndefinedValueError:
        print "execution interrupted:"
        print sys.exc_value
    elif sys.exc_type is insight.error.BreakpointReached:
        (id, s) = sys.exc_value
        print "stop condition {} reached: {}".format(id, s)
    elif sys.exc_type is insight.error.SinkNodeReached:
        (ga, la) = sys.exc_value
        print "sink node reached after(0x{:x}, {})".format(ga, la)
    elif sys.exc_type is insight.error.JumpToInvalidAddress:
        (ga, la) = sys.exc_value
        print "try to jump into undefined memory(0x{:x}, {})".format(ga, la)
    elif sys.exc_type is insight.error.NotDeterministicBehaviorError:
        print "stop in a configuration with several output arrows"
    elif sys.exc_type is insight.error.SimulationNotStartedException:
        print "simulator is not running"
    elif sys.exc_type is insight.error.CodeChangedException:
        (ga, la) = sys.exc_value
        print "code has been changed since last visit at address", \
            "(0x{:x}, {:d})".format (ga, la)
    elif sys.exc_type is NotImplementedError:
        print "feature not supported."
    else:
        raise


def view_asm(start=None, end=None, ep=None):
    """
    Display a CFG of the microcode discovered til then.

    This function display a CFG of the microcode that have been run
    through til then. It uses the xdot application to visualize the
    CFG as a DOT graph.

    Parameters:
    - start : set the address of the starting node (entrypoint if None)
    - end   : set the address of an end node (no end node if None)
    - ep    : set the entry point address
    """
    def reset_viewer(arg):
        global dotviewer
        dotviewer = None

    def basic_block_clicked(widget, nodeid, url, event):
        if nodeid is None:
            return False
        return True
    import gtk.keysyms
    def key_pressed_event(widget, event):
        global simulator, startpoint, dotviewer
        if event.keyval == gtk.keysyms.s:
            step ()
            return True
        if event.keyval == gtk.keysyms.r:
            run ()
            return True
        if event.keyval == gtk.keysyms.c:
            cont ()
            return True
        return False

    global simulator, startpoint, dotviewer
    if simulator is None:
        print "Program is not started"
        return
    addrspace = simulator.get_microcode().get_range()
    if start is None:
        start = addrspace[0]
    if end is None:
        end = addrspace[1]
    if ep is None:
        ep = pc()
    dotstring = simulator.get_microcode().dot(ep, start, end)
    if dotviewer is None:
        dotviewer = xdot.DotWindow()
        dotviewer.connect('destroy', reset_viewer)
        dotviewer.widget.connect('clicked', basic_block_clicked)
        dotviewer.widget.connect('key-press-event', key_pressed_event)
        dotviewer.show()
    dotviewer.set_dotcode(dotstring)


def view_mc(ep=None):
    """
    Parameters:
    - ep    : set the entry point address
    """
    def reset_viewer(arg):
        global dotviewer
        dotviewer = None

    global simulator, startpoint, dotviewer
    if simulator is None:
        print "Program is not started"
        return
    if ep is None:
        ep = startpoint
    dotstring = simulator.get_microcode().cfg(start = ep)
    if dotviewer is None:
        dotviewer = xdot.DotWindow()
        dotviewer.connect('destroy', reset_viewer)
        dotviewer.show()
    dotviewer.set_dotcode(dotstring)


def steps():
    """
    Return current simulation steps.

    The simulator records calls to simulation functions: run, step, cont,
    microstep. This function returns the list of calls which can be
    memorized for later use. The content of the record can be displayed
    using 'display_steps' and the sequence can re-executed using
    'replay_steps'.
    """
    global recorder
    if recorder is None:
        print "nothing has been recorded"
        return None
    result = []
    for r in recorder:
        result += [ r ]
    return result


def replay_steps(s):
    """
    Re-execute a sequence of simulation steps.

    Parameters:
    s : the sequence of steps returned by a prior call to 'steps()'
    """
    if s is None:
        print "nothing to do"
        return
    for (addr,action,arg) in s:
        action(arg)


def display_steps(s, asrecord = False):
    """
    Display a sequence of simulation steps.

    Parameters:
    s        : the simulation steps as returned by 'steps()'.
    asrecord : if True the records are displayed as a Python code.
    """
    if s is None:
        print "nothing to display"
        return
    if asrecord:
        sys.stdout.write("[");
        l = len(s)
        for i in range(l):
            fmt = "(0x{:x},{}, 0x{:x})"
            if i != l - 1:
                fmt += ", "
            rec = s[i]
            sys.stdout.write(fmt.format(rec[0], rec[1].__name__, rec[2]))
        print "]"
    else:
        for (addr, action, arg) in s:
            print "0x{:x} : {}({})".format(addr, action.__name__, arg)


def display_stack(start, end, absconv, bp = None, sp = None):
    """
    Display the content of the stack.

    The function dumps the content of a memory area identified as the stack
    of the program. Dump is done from greatest addresses to lowest. The user
    has to furnish a function able to convert abstract values (according to
    current evaluation domain) in concrete ones.

    Each line of the output contains:
    - the address aligned to the size of a word (see 'info("word_size")'),
    - the raw and hexadecimal value of bytes; a dot is displayed in place
      of a non-convertible or non-printable byte
    - if values of the frame and stack pointer are given ('bp' and 'sp' pa-
      rameters) the relative position to these pointers are given.

    Parameters:
    - start   : start address of the stack
    - end     : end address of the stack
    - absconv : a function that convert an abstract byte into a concrete
                byte
    - bp      : current value of the frame pointer
    - sp      : current value of the stack pointer
    """
    global simulator
    if simulator is None:
        print "program is not started"
        return

    if start < end:
        end, start = start, end

    addrsize = prog().info()["address_size"] / 8
    elsize = prog().info()["word_size"] / 8

    start -= start % elsize
    while start >= end :
        bytestr = ""
        strstr = ""
        for i in range(elsize):
            try:
                byte = absconv(simulator.get_memory(start + i, 1)[0])
            except IndexError:
                byte = None

            if byte is None:
                bytestr += ".."
                strstr += "."
            else:
                bytestr += "{:02x}".format (byte)
                c = chr(byte)
                if c not in string.printable or \
                   (c in string.whitespace and c != " "):
                    c = "."
                strstr += c
        fmt = "0x{:" + str(addrsize) + "x} : {} {} ; {} {}"
        if bp is not None:
            bps = "<bp{:+x}>".format(start - bp)
        else:
            bps = ""
        if sp is not None:
            sps = "<sp{:+x}>".format(start - sp)
        else:
            sps = ""
        print fmt.format(start, bytestr, strstr, bps, sps)
        start -= elsize


def eval(expr):
    """
    Evaluate an expression according to the current state of the memory.

    Parameters:
    - expr : a string containing the expression to be evaluated

    Returns:
    - a string with the value of 'expr'.
    """
    global simulator

    if simulator is None:
        print "program is not running"
        return
    return simulator.eval (expr)


def display(expr, alias = None):
    """
    Display an expression after each simulation step.

    The simulator maintains a list of expressions evaluated and displayed
    after each simulation function (step, microstep, run, cont). The
    function display couples of 'expr = val' where 'expr' is the string
    specified by the user and 'val' the evaluation of 'expr' according to
    the current state and simulation domain. In the displayed list' expr'
    can be replaced by an 'alias'.

    Parameters:
    - expr  : a string containing the expression to display
    - alias : if not None the value is display in place of expr as a
              description of the expression
    """
    global simulator, displayed_expressions

    if simulator is None:
        print "program is not running"
        return
    if not isinstance(expr, str) or (alias is not None and \
                                     not isinstance(alias, str)):
        raise TypeError
    if not __display_expressions in hooks[run]:
        add_run_hook (__display_expressions)
        add_step_hook (__display_expressions)
        add_cont_hook (__display_expressions)
        add_microstep_hook (__display_expressions)
    displayed_expressions += [(alias, expr)]

def undisplay(index):
    """
    Remove a displayed expression.

    Parameters:
    - index : index of the expression in the list given by 'display'
    """
    global simulator, displayed_expressions

    if simulator is None:
        print "program is not running"
        return
    if index in range (len(displayed_expressions)):
        displayed_expressions[index:index+1] = []


def assume(addr, cond, l = 0):
    """
    Attach a Boolean constraint to a microcode address.

    The function associates to microcode address (addr, l) the constraint
    'cond'. Each time the simulator encounters the given address the path
    condition is contrained with 'cond'.

    Parameters:
    - addr : global component of the microcode address
    - cond : a string containing the constraint
    - l : the local component of the microcode address
    """
    global simulator
    if simulator is None:
        print "program is not running"
        return
    if not isinstance(cond, str):
        raise TypeError, "expect an expression given as a string"

    try:
        simulator.assume(addr, cond, l)
    except:
        simulation_error()

def remove_assumption(g, l = 0):
    """
    Remove assumption at microcode address (g,l).

    Parameters:
    - g : global component of the microcode address
    - l : local component of the microcode address
    """
    global simulator
    if simulator is None:
        print "program is not running"
        return
    try:
        simulator.remove_assumption(g,l)
    except:
        simulation_error()

def set_compare_state():
    """
    Mark current state as comparison reference.

    The function memorizes the current state of registers and memory to be
    compared later with a future state. This feature is mainly used to
    understand the effect of a sequence of instructions on the state.

    If a state is already memorized then it is forgotten.
    """
    global simulator
    if simulator is None:
        print "program is not running"
        return
    simulator.set_compare_state()

def unset_compare_state():
    """
    Unmark current state used for comparisons.

    The function is just an explicit release of resources allocated to the
    state used for comparisons.
    """
    global simulator
    if simulator is None:
        print "program is not running"
        return
    simulator.unset_compare_state()

def compare_states():
    """
    Compare current state with the one marked for comparison.

    The function display the registers and memory cells that differ between
    the compared states i.e. the current one and the one marked for using
    'set_compare_state' function.
    """
    global simulator
    if simulator is None:
        print "program is not running"
        return
    diffs = simulator.compare_states()
    if diffs is None:
        return
    print "state comparison:"
    for (loc, v1, v2) in diffs:
        if isinstance(loc,str):
            print loc, v1, v2
        else:
            print "0x{:x}".format (loc), v1, v2

def __record(addr, fun, arg, reset = False):
    global recorder;
    if reset:
        recorder = []
    recorder += [(addr, fun, arg)]


def __display_expressions():
    global displayed_expressions
    i = 0
    for alias,expr in displayed_expressions:
        if alias is None:
            alias = expr
        print "{:d}) {} = {}".format(i, alias, eval(expr))
        i += 1
