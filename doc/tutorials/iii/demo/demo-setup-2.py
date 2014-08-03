# mandatory import to be able to use Insight functions
from insight.debugger import *
from insight.iii import *

# we load the binary file
binfile ("crackme", target="elf32-i386", domain="symbolic")

# load the stub replacing __libc_start_main
load_stub ("stub_libc_start_main.mc.xml", P ().sym ("__libc_start_main"), True)
# ADDED TO demo-setup-1
load_stub ("stub_printf.mc.xml", P ().sym ("__printf"), True)
load_stub ("stub_read.mc.xml", P ().sym ("__read"), True)

# useful hooks
def init_registers ():
    valregs = { 
        'ebp' : 0xFFFFFFF0,
        'esp' : 0xFFFFFFF0,
        'df' : 0  # necessary for sting operations
    }
    for r in P().info()['registers']:
        if r in valregs:
          val = valregs[r]
          set(r, val)

# filter functions
# ADDED TO demo-setup-1
import re

def filter_abstract_byte (val):
    """translate a concrete "abstract" value into a character"""
    p = re.compile('^(0x[0-9A-Fa-f]{1,2})\{.*\}$')
    m = p.match (val)
    if m is not None:
        return chr(int(m.group(1),16))
    else:
        return val

add_hook (run, init_registers)

add_hook (cont, view_asm)
add_hook (run, view_asm)
add_hook (step, view_asm)


# start simulation from entrypoint
run ()
cont()

