import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            m = max(m,abs(l))
    return m

def randomBool():
    return bool(random.getrandbits(1))

def exportCNF(clauses, filename, ind = []):
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

#parse .gcnf instance,
#returns a pair C,B where B contains the base (hard) clauses and C the other clauses
def parse(filename):
    C = []
    B = []
    with open(filename, "r") as f:
        lines = f.readlines()
        if filename[-5:] == ".gcnf":
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[1:-1]]
                if len(cl) > 0:
                    if line[0] == "{0}":
                        B.append(cl)
                    else:
                        C.append(cl)
        else:
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[:-1]]
                if len(cl) > 0:
                    C.append(cl)
    return C,B

class Counter:
    def __init__(self, filename, e, d):
        self.filename = filename
        self.C, self.B = parse(filename)
        self.dimension = len(self.C)
        self.XOR = None
        self.tresh = 1 + 9.84 * (1 + (e / (1 + e)))*(1 + 1/e)*(1 + 1/e)
        self.t = int(17 * log(3 / d,2));
        self.checks = 0
        self.rid = randint(1,10000000)

    def exportSS(self):
        clauses = []
        xclauses = []

        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            clauses.append(renumCl)
        return clauses, [i for i in range(1, self.dimension + 1)]

    def exportBSS(self):
        clauses = []
        xclauses = []

        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1

        #max model
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: 
                    clauses.append([-i, -(l + self.dimension)])
                else:
                    clauses.append([-i, -(l - self.dimension)])
            i += 1

        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            clauses.append(renumCl)
        return clauses, [i for i in range(1, self.dimension + 1)]


    def exportBLSS(self):
        clauses = []
        xclauses = []

        #S is sat
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1

        #the base clauses
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            clauses.append(renumCl)

        #max model
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: 
                    clauses.append([-i, -(l + 2*self.dimension)])
                else:
                    clauses.append([-i, -(l - 2*self.dimension)])
            i += 1

        #E is sat
        i = 1
        mv = maxVar(clauses)
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + mv)
                else: renumCl.append(l - mv)
            renumCl.append(i + self.dimension)
            clauses.append(renumCl)
            i += 1

        #the base clauses
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + mv)
                else: renumCl.append(l - mv)
            clauses.append(renumCl)

        #E supseteq S
        for i in range(1, self.dimension + 1):
            clauses.append([i, - (i + self.dimension)])

        proper = []
        mv = maxVar(clauses)
        act = mv
        for i in range(1, self.dimension + 1):
            act += 1
            proper += [[act, i], [act, -(i + self.dimension)]] 
        proper.append([-a for a in range(mv + 1, act + 1)])

        clauses += proper

        return clauses, [i for i in range(1, self.dimension + 1)]

    def exportLSS(self):
        clauses = []
        xclauses = []

        #S is sat
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1

        #E is sat
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            renumCl.append(i + self.dimension)
            clauses.append(renumCl)
            i += 1

        #the base clauses
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + 2*self.dimension)
                else: renumCl.append(l - 2*self.dimension)
            clauses.append(renumCl)

        #E supseteq S
        for i in range(1, self.dimension + 1):
            clauses.append([i, - (i + self.dimension)])

        proper = []
        mv = maxVar(clauses)
        act = mv
        for i in range(1, self.dimension + 1):
            act += 1
            proper += [[act, i], [act, -(i + self.dimension)]] 
        proper.append([-a for a in range(mv + 1, act + 1)])

        clauses += proper

        return clauses, [i for i in range(1, self.dimension + 1)]

    def run(self):
        SSClauses, SSInd = self.exportSS()
        SSFile = "/var/tmp/SS.cnf"
        exportCNF(SSClauses, SSFile, SSInd)
        print(SSFile)
        
        LSSClauses, LSSInd = self.exportLSS()
        LSSFile = "/var/tmp/LSS.cnf"
        exportCNF(LSSClauses, LSSFile, LSSInd)
        print(LSSFile)

        BSSClauses, BSSInd = self.exportBSS()
        BSSFile = "/var/tmp/BSS.cnf"
        exportCNF(BSSClauses, BSSFile, BSSInd)
        print(BSSFile)

        BLSSClauses, BLSSInd = self.exportBLSS()
        BLSSFile = "/var/tmp/BLSS.cnf"
        exportCNF(BLSSClauses, BLSSFile, BLSSInd)
        print(BLSSFile)

def restricted_float(x):
    try:
        x = float(x)
    except ValueError:
        raise argparse.ArgumentTypeError("%r not a floating-point literal" % (x,))

    if x < 0.0 or x > 1.0:
        raise argparse.ArgumentTypeError("%r not in range [0.0, 1.0]"%(x,))
    return x

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("--epsilon", "-e", type = float, help = "Set the epsilon parameter, i.e., controls the approximation factor of the algorithm. Allowed values: float (> 0). Default value is 0.8.", default = 0.8)
    parser.add_argument("--delta", "-d", type = restricted_float, help = "Set the delta parameter, i.e., controls the probabilistic guarantees of the algorithm. Allowed values: float (0-1). Default value is 0.2.", default = 0.2)
    parser.add_argument("--threshold", type = int, help = "Set manually the value of threshold. By default, the value of threshold is computed based on the epsilon parameter to guarantee the approximate guarantees that are required/set by epsilon. If you set threshold manually, you affect the guaranteed approximate factor of the algorithm.")
    parser.add_argument("--iterations", type = int, help = "Set manually the number of iterations the algorithm performs to find the MUS count estimate. By default, the number of iterations is determined by the value of the delta parameter (which controls the required probabilistic guarantees). By manually setting the number of iterations, you affect the probabilistic guarantees.")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    args = parser.parse_args()

    counter = Counter(args.input_file, args.epsilon, args.delta)
    if args.threshold is not None:
        counter.tresh = args.threshold
    if args.iterations is not None:
        counter.t = args.iterations

    print("epsilon guarantee:", args.epsilon)
    print("delta guarantee:", args.delta)
    print("threshold", counter.tresh)
    print("iterations to complete:", counter.t)
    counter.run()
