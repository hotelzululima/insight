import sys
import string


def pretty_print_memory(P, s, l=16):
    if P is None:
        raise ValueError
    for addr, data in P.dump_memory(start=s, len=l):
        sys.stdout.write("{0:08x} :".format(addr))
        st = " "
        for i in range(0, len(data)):
            b = data[i]
            if i % 2 == 0:
                print " ",
            if b is None:
                sys.stdout.write("  ")
                st += " "
            else:
                sys.stdout.write("{0:02x}".format(b))
                c = chr(b)
                if not c in string.printable or \
                   (c in string.whitespace and c != " "):
                    c = "."
                st += c
        print st


def pretty_disas_memory(P, s, l=16):
    if P is None:
        raise ValueError
    for instr in P.disas(s, l):
        print " {:x} :\t{}".format(instr[0], instr[1])
