# mandatory import to be able to use Insight functions
from insight.debugger import *
from insight.iii import *

# we load the binary file
binfile ("crackme", target="elf32-i386", domain="symbolic")

# load the stub replacing __libc_start_main
load_stub ("stub_libc_start_main.mc.xml", P ().sym ("__libc_start_main"))

# initialization of register 
valregs = { 
    'esp' : 0xFFFFFFF0,
    'df' : 0  # mandatory for string operations
}

# useful hooks
def init_registers ():
    global valregs
    for r in P().info()['registers']:
        if r in valregs:
          val = valregs[r]
          set(r, val)

add_hook (run, init_registers)

add_hook (cont, view_asm)
add_hook (run, view_asm)
add_hook (step, view_asm)

# start simulation from entrypoint
run ()
cont()

