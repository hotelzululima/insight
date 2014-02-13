import sys
import string

def pretty_print_memory (P):
    if P is None:
        raise ValueError
    for addr, data in P.dump_memory (0, step=16):
        sys.stdout.write ("{0:08x} :".format (addr));
        st = " "
        for i in range (0,len(data)):
            b = data[i]
            if i % 2 == 0:
                print " ",
            if b is None:
                sys.stdout.write ("  ")
                st += " "
            else:
                sys.stdout.write ("{0:02x}".format (b))
                c = chr (b)  
                if not c in string.printable or (c in string.whitespace and c != " "):
                    c = "."
                st += c
        print st



