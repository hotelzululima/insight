import utils
import sys
import io

program = None
simulator = None

def f(filename,target="elf32-i386"):
    global program
    program = io.load_bfd (filename, target)


def r():
    global simulator, program
    if program == None:
        if len (sys.argv) == 2:
            f (sys.argv[1])
        elif len (sys.argv) == 3:
            f (sys.argv[1],sys.argv[2])
    if program == None:
        raise RuntimeWarning, "No program has been loaded"

    config.set ("kernel.expr.solver.name", "mathsat")
    simulator = program.simulator ()
    for a in simulator.run ():
        print a

def ms(a):
    global simulator
    for a in simulator.microstep (a):
        print a

def s():
    global simulator
    for a in simulator.step ():
        print a

