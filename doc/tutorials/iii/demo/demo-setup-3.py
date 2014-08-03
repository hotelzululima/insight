# mandatory import to be able to use Insight functions
from insight.debugger import *
from insight.iii import *

# we load the binary file
binfile ("crackme", target="elf32-i386", domain="symbolic")

# load the stub replacing __libc_start_main
load_stub ("stub_libc_start_main.mc.xml", P ().sym ("__libc_start_main"), True)
load_stub ("stub_printf.mc.xml", P ().sym ("__printf"), True)
load_stub ("stub_read.mc.xml", P ().sym ("__read"), True)

# useful hooks
def init_registers ():
    valregs = { 
        'esp' : 0xFFFFFFF0,
        'df' : 0  # mandatory for string operations
    }
    for r in P().info()['registers']:
        if r in valregs:
          val = valregs[r]
          set(r, val)

# filter functions
import re

def filter_abstract_byte (val):
    """translate a concrete "abstract" value into a character"""
    p = re.compile('^(0x[0-9A-Fa-f]{1,2})\{.*\}$')
    m = p.match (val)
    if m is not None:
        return chr(int(m.group(1),16))
    else:
        return val

# setting hooks
add_hook (run, init_registers)
for f in [cont, run, step]: add_hook(f, view_asm)

# conditional breakpoint to stop just after the loop that checks
# if the password given by the user is correct.
breakpoint(0x8048e17)
cond(1, "(EQ %ecx 1)")

# start the simulator
run()

# assumption must be introduced after the simulation is started
assume(0x8048e15, "%zf")

# start the computation until the breakpoint is reached.
cont()
# go out of the loop
step()
# let the SMT solver gives us valid input character
for i in range(8): set(0x8048d45+i)
# display the password
dump(0x8048d45, l = 8, filter = filter_abstract_byte)

