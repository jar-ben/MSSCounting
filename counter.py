import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse
import os
from functools import partial
import signal

def receiveSignal(tempFiles, signalNumber, frame):
    print(tempFiles, signalNumber, frame)
    print('Received signal:', signalNumber)
    print('Cleaning tmp files')
    for f in tempFiles:
        if os.path.exists(f):
            print("removing", f, "...", end="")
            os.remove(f)
            print("removed")
    sys.exit()


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

def exportCNF(clauses, filename, ind, varFile):
    print("running export for ", filename)
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

    print(varFile)
    with open(varFile, "w") as f:
        f.write(",".join ([str(v) for v in ind]))

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

def offsetClause(cl, off):
    return [offset(l, off) for l in cl]    

class Counter:
    def __init__(self, filename, useAutarky):
        self.variant = "base"
        self.filename = filename
        self.C, self.B = parse(filename)
        self.autarky = useAutarky
        if self.autarky and filename[-4:] == ".cnf":
            self.autarkyTrim()
        self.dimension = len(self.C)
        self.maxVar = 2*self.dimension + 2*maxVar(self.C + self.B)
        self.XOR = None
        self.checks = 0
        self.rid = randint(1,10000000)
        flatten = []
        for cl in (self.B + self.C):
            flatten += cl
        self.lits = set([l for l in flatten])
        self.hitmapC = {}
        self.hitmapB = {}
        for l in self.lits:
            self.hitmapC[l] = []
            self.hitmapC[-l] = []
            self.hitmapB[l] = []
            self.hitmapB[-l] = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                assert l in self.lits
                self.hitmapC[l].append(i + 1) #+1 offset
        for i in range(len(self.B)):
            for l in self.B[i]:
                assert l in self.lits
                self.hitmapB[l].append(i) #note that here we store 0-based index as opposed to hitmapC

        #selection variables for individual wrappers. True means selected
        self.w2 = False
        self.w3 = False
        self.w4 = False
        self.w5 = False

        self.SSFile = "/var/obj/xbendik/SS_{}.cnf".format(self.rid)
        self.SSIndFile = self.SSFile[:-4] + "_ind.cnf"
        self.LSSFile = "/var/obj/xbendik/LSS_{}.cnf".format(self.rid)
        self.LSSIndFile = self.LSSFile[:-4] + "_ind.cnf"
        self.tmpFiles = [self.SSFile, self.SSIndFile, self.LSSFile, self.LSSIndFile]

    def autarkyTrim(self):
        assert self.B == []
        cmd = "timeout 3600 python3 autarky.py {}".format(self.filename)
        print(cmd)
        out = run(cmd, 3600)
        if "autarky vars" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    autarky = [int(c) - 1 for c in line.split()[1:]]
        else: return
        coAutarky = [i for i in range(len(self.C)) if i not in autarky]
        C = [self.C[c] for c in autarky]
        B = [self.C[c] for c in coAutarky]
        print("autarky size: {} of {} clauses".format(len(autarky), len(self.C)))
        self.C, self.B = C, B

    def SS(self):
        clauses = self.W1()
        if self.w4:
            clauses += self.W4()
        if self.w5:
            act = max(self.maxVar, maxVar(clauses))
            clauses += self.W5(act)

        inds = [i for i in range(1, self.dimension + 1)]
        return clauses, inds

    def LSS(self):
        clauses, inds = self.SS()
        act = max(self.maxVar, maxVar(clauses))
        clauses += self.nonMSSBase(act)
        return clauses, inds


    #VARIABLES INFO
    #Activation literals A: 1 -- dimension
    #Activation literals B: dimension + 1 -- 2*dimension
    #F's variables: 2*dimension + 1 -- 2*dimension + Vars(F)
    #F's primed variables: 2*dimension + Vars(F) + 1 -- 2*dimension + 2*Vars(F)
    def W1(self):
        clauses = []

        i = 1
        for cl in self.C:
            renumCl = offsetClause(cl, 2*self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            clauses.append(offsetClause(cl, 2*self.dimension))
        return clauses

    def nonMSSBase(self, act):
        clauses = []
        #the superset E is satisfiable
        i = 1
        maxCB = maxVar(self.C + self.B)
        for cl in self.C:
            renumCl = offsetClause(cl, 2*self.dimension + maxCB)
            renumCl.append(i + self.dimension)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            clauses.append(offsetClause(cl, 2*self.dimension + maxCB))
        

        #E supseteq S
        for i in range(1, self.dimension + 1):
            clauses.append([i, - (i + self.dimension)])

        proper = []
        mv = act
        for i in range(1, self.dimension + 1):
            act += 1
            proper += [[act, i], [act, -(i + self.dimension)]] 
        proper.append([-a for a in range(mv + 1, act + 1)])

        clauses += proper
        return clauses

    def W4(self):
        clauses = []
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

        return clauses

    def W5(self, act):
        clauses = []
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
            #break  
        return clauses


    def parseGanak(self, out):
        if "# END" not in out: return -1
        reading = False
        for line in out.splitlines():
            if reading:
                return int(line.rstrip().split()[-1])
            if "# solutions" in line: reading = True

    def parseProjMC(self, out):
        for line in out.splitlines():
            if line[:2] == "s ":
                return int(line.rstrip().split()[1])

    def runExact(self):
        self.ganak = True
        SSClauses, SSInd = self.SS()
        if len(SSClauses) > 1200000:
            print("Too large wrapper,", str(len(SSClauses)), "terminating")
            sys.exit()
        SSFile = self.SSFile
        SSIndFile = self.SSIndFile
        exportCNF(SSClauses, SSFile, SSInd, SSIndFile)
        print(SSFile)
        
        LSSClauses, LSSInd = self.LSS()
        if len(LSSClauses) > 1200000:
            print("Too large wrapper,", str(len(LSSClauses)), "terminating")
            sys.exit()
        LSSFile = self.LSSFile
        LSSIndFile = self.LSSIndFile
        exportCNF(LSSClauses, LSSFile, LSSInd, LSSIndFile)
        print(LSSFile)

        timeout = 3600
        if self.ganak:
            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, SSFile)
            print(cmd)
            SScount = self.parseGanak(run(cmd, timeout))
            print("SS count:", SScount)

            cmd = "timeout {} /home/xbendik/bin/ganak/build/ganak {}".format(timeout, LSSFile)
            print(cmd)
            LSScount = self.parseGanak(run(cmd, timeout))
            print("LSS count:", LSScount)
        else:
            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, SSFile, SSIndFile)
            print(cmd)
            SScount = self.parseProjMC(run(cmd, timeout))
            print("SS count:", SScount)

            cmd = "timeout {} ./projMC_linux {} -fpv=\"{}\"".format(timeout, LSSFile, LSSIndFile)
            print(cmd)
            LSScount = self.parseProjMC(run(cmd, timeout))
            print("LSS count:", LSScount)
         
        MSScount = -1
        if (SScount >= 0) and (LSScount >= 0): MSScount = SScount - LSScount
        print("MSS count:", MSScount)
        os.remove(LSSFile)
        os.remove(LSSIndFile)
        os.remove(SSFile)
        os.remove(SSIndFile)

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("--variant", help = "Type of endocing (allowed values = {base,B,FEB}", default = "base")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    parser.add_argument("--w2", action='store_true', help = "Use the wrapper W2, i.e., autarky (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w3", action='store_true', help = "Use the wrapper W3 (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w4", action='store_true', help = "Use the wrapper W4 (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w5", action='store_true', help = "Use the wrapper W5 (multiple wrappers can be used simultaneously)")
    args = parser.parse_args()

    print(args.w2, args.w4, args.w5)

    counter = Counter(args.input_file, args.w2)
    signal.signal(signal.SIGHUP, partial(receiveSignal, counter.tmpFiles))
    signal.signal(signal.SIGINT, partial(receiveSignal, counter.tmpFiles))
    signal.signal(signal.SIGTERM, partial(receiveSignal, counter.tmpFiles))

    counter.variant = args.variant
    counter.w2 = args.w2
    counter.w4 = args.w4
    counter.w5 = args.w5

    counter.runExact()
