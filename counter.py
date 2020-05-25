import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse

def run(cmd, timeout, ttl = 3):
    proc = sp.Popen([cmd], stdout=sp.PIPE, stderr=sp.PIPE, shell=True)
    try:
        (out, err) = proc.communicate(timeout = int(timeout * 1.1) + 1)
        out = out.decode("utf-8")
    except sp.TimeoutExpired:
        proc.kill()
        try:
            (out, err) = proc.communicate()
            out = out.decode("utf-8")
        except ValueError:
            if ttl > 0:
                return run(cmd, timeout, ttl - 1)
            out = ""
    return out

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

def offset(a, off):
    if a > 0:
        return a + off
    return a - off

class Counter:
    def __init__(self, filename, e, d):
        self.variant = "base"
        self.filename = filename
        self.C, self.B = parse(filename)
        self.autarky = True
        if self.autarky and filename[-4:] == ".cnf":
            self.autarkyTrim()

        self.dimension = len(self.C)
        self.XOR = None
        self.tresh = 1 + 9.84 * (1 + (e / (1 + e)))*(1 + 1/e)*(1 + 1/e)
        self.t = int(17 * log(3 / d,2));
        self.checks = 0
        self.rid = randint(1,10000000)
        flatten = []
        for cl in (self.B + self.C):
            flatten += cl
        self.lits = set([l for l in flatten])
        self.hitmapC = {l:[] for l in self.lits}
        for i in range(len(self.C)):
            for l in self.C[i]:
                assert l in self.lits
                self.hitmapC[l].append(i + 1) #+1 offset
        self.hitmapB = {l:[] for l in self.lits}
        for i in range(len(self.B)):
            for l in self.B[i]:
                assert l in self.lits
                self.hitmapB[l].append(i) #note that here we store 0-based index as opposed to hitmapC

    def autarkyTrim(self):
        assert self.B == []
        out = run("timeout 3600 python3 autarky.py {}".format(self.filename), 3600)
        if "autarky vars" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    autarky = [int(c) - 1 for c in line.split()[1:]]
        coAutarky = [i for i in range(len(self.C)) if i not in autarky]
        C = [self.C[c] for c in autarky]
        B = [self.C[c] for c in coAutarky]
        print("autarky size: {} of {} clauses".format(len(autarky), len(self.C)))
        self.C, self.B = C, B

    def SS(self):
        if self.variant == "base":
            return self.exportSS()
        elif self.variant == "B":
            return self.exportBSS()
        elif self.variant == "FEB":
            return self.exportFEBSS()
        assert False

    def LSS(self):
        if self.variant == "base":
            return self.exportLSS()
        elif self.variant == "B":
            return self.exportBLSS()
        elif self.variant == "FEB":
            return self.exportFEBLSS()
        assert False

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

        #base clauses
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            clauses.append(renumCl)
        return clauses, [i for i in range(1, self.dimension + 1)]

    def exportEBSS(self):
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

        for key in self.hitmapC:
            if len(self.hitmapC[key]) == 0: continue
            if key > 0:
                lit = key + self.dimension
            else:
                lit = key - self.dimension
            clauses.append([-lit] + [ -l for l in self.hitmapC[key]])

        return clauses, [i for i in range(1, self.dimension + 1)]


    def exportFEBSS(self):
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

        #base clauses
        for cl in self.B:
            renumCl = []
            for l in cl:
                if l > 0: renumCl.append(l + self.dimension)
                else: renumCl.append(l - self.dimension)
            clauses.append(renumCl)

        #E encoding
        for key in self.hitmapC:
            if len(self.hitmapC[key]) == 0: continue
            if key > 0:
                lit = key + self.dimension
            else:
                lit = key - self.dimension
            clauses.append([-lit] + [ -l for l in self.hitmapC[key]])

        #F encoding
        act = maxVar(clauses)
        for i in range(len(self.C)):
            for l in self.C[i]:
                cl = [-i]
                acts = []
                for d in self.hitmapC[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-d] + [-offset(k, self.dimension) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:             
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, self.dimension) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-(i + 1)] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
            #break

        return clauses, [i for i in range(1, self.dimension + 1)]
    
    def exportFEBLSS(self):
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

        #F encoding
        act = maxVar(clauses)
        for i in range(len(self.C)):
            for l in self.C[i]:
                cl = [-i]
                acts = []
                for d in self.hitmapC[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-d] + [-offset(k, 2*self.dimension) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:             
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, 2*self.dimension) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-(i + 1)] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
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

    def approxMC(self, filename):
        timeout = 3600
        cmd = "timeout {} approxmc {}".format(timeout, filename)
        out = run(cmd, timeout)
        for line in out.splitlines():
            if "Number of solutions is" in line:
                line = line.split("Number of solutions is:")[1].strip()
                assert "x" in line
                line = line.split("x")
                coeff = int(line[0].strip())
                base = line[1].strip().split("^")[0]
                exp = line[1].strip().split("^")[1]
                return coeff, base, exp
        print("timeout")
        assert False

    def parseGanak(self, out):
        if "# END" not in out: return -1
        reading = False
        for line in out.splitlines():
            if reading:
                return int(line.rstrip().split()[-1])
            if "# solutions" in line: reading = True

    def runExact(self):
        SSClauses, SSInd = self.SS()
        SSFile = "/var/tmp/SS_{}.cnf".format(self.rid)
        exportCNF(SSClauses, SSFile, SSInd)
        print(SSFile)
        
        LSSClauses, LSSInd = self.LSS()
        LSSFile = "/var/tmp/LSS_{}.cnf".format(self.rid)
        exportCNF(LSSClauses, LSSFile, LSSInd)
        print(LSSFile)

        timeout = 3600
        cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, SSFile)
        SScount = self.parseGanak(run(cmd, timeout))
        print("SS count:", SScount)

        cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, LSSFile)
        LSScount = self.parseGanak(run(cmd, timeout))
        print("LSS count:", LSScount)

        print("MSS count:", SScount - LSScount)

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

        EBSSClauses, EBSSInd = self.exportEBSS()
        EBSSFile = "/var/tmp/EBSS.cnf"
        exportCNF(EBSSClauses, EBSSFile, EBSSInd)
        print(EBSSFile)

        FEBSSClauses, FEBSSInd = self.exportFEBSS()
        FEBSSFile = "/var/tmp/FEBSS.cnf"
        exportCNF(FEBSSClauses, FEBSSFile, FEBSSInd)
        print(FEBSSFile)

        FEBLSSClauses, FEBLSSInd = self.exportFEBLSS()
        FEBLSSFile = "/var/tmp/FEBLSS.cnf"
        exportCNF(FEBLSSClauses, FEBLSSFile, FEBLSSInd)
        print(FEBLSSFile)
        #BSScoeff, BSSbase, BSSexp = self.approxMC(BSSFile)
        #BLSScoeff, BLSSbase, BLSSexp = self.approxMC(BLSSFile)
        #print(BSScoeff, BSSbase, BSSexp)
        #print(BLSScoeff, BLSSbase, BLSSexp)

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
    parser.add_argument("--variant", help = "Type of endocing (allowed values = {base,B,FEB}", default = "base")
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
    counter.variant = args.variant

    print("epsilon guarantee:", args.epsilon)
    print("delta guarantee:", args.delta)
    print("threshold", counter.tresh)
    print("iterations to complete:", counter.t)
    #counter.run()
    counter.runExact()
