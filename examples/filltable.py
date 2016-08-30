import re

def giveMeInfo(theFile):
    text = 0
    declarations = 0
    expressions = 0
    terms = 0
    sets = 0 
    definitions = 0
    f = open(theFile, "r")
    for line in f:
        lineswithtext = re.findall(r'\\text', line)
        lineswithdeclaration = re.findall(r'\\declaration', line)
        lineswithexpression = re.findall(r'\\expression', line)
        lineswithterms= re.findall(r'\\term', line)
        lineswithsets= re.findall(r'\\set', line)
        lineswithdefinitions = re.findall(r'\\definition', line)
        if lineswithtext:
            t = len(lineswithtext)
            text = text + t
        if lineswithdeclaration:
            t = len(lineswithdeclaration)
            declarations = declarations + t
        if lineswithexpression:
            t = len(lineswithexpression)
            expressions = expressions + t
        if lineswithterms:
            t = len(lineswithterms)
            terms = terms + t
        if lineswithsets:
            t = len(lineswithsets)
            sets = sets + t
        if lineswithdefinitions:
            t = len(lineswithdefinitions)
            definitions = definitions + t
    print theFile + ", text:" + str(text) + ", declarations:" + str(declarations) + ", expressions:" + str(expressions) + ", terms:" + str(terms) + ", sets:" + str(sets) + ", definitions:" + str(definitions)
    print "\n"        
    f.close()
    
def giveMeInfoForZDRa(theFile):
    SS =0
    IS =0
    CS =0
    OS =0
    TS =0
    PRE =0
    PO=0
    O=0
    A=0
    SI=0
    f = open(theFile, "r")
    for line in f:
        lineswith_A = re.findall(r'\\draschema\{A', line)
        lineswith_SS = re.findall(r'\\draschema\{SS', line)
        lineswith_IS = re.findall(r'\\draschema\{IS', line)
        lineswith_CS= re.findall(r'\\draschema\{CS', line)
        lineswith_OS= re.findall(r'\\draschema\{OS', line)
        lineswith_TS = re.findall(r'\\draschema\{TS', line)
        lineswithline_TS = re.findall(r'\\draline\{TS', line)
        lineswith_PRE = re.findall(r'\\draschema\{PRE', line)
        lineswithline_PRE = re.findall(r'\\draline\{PRE', line)
        lineswith_PO = re.findall(r'\\draschema\{PO', line)
        lineswithline_PO = re.findall(r'\\draline\{PO', line)
        lineswith_O = re.findall(r'\\draschema\{O', line)
        lineswithline_O = re.findall(r'\\draline\{O', line)
        lineswith_SI = re.findall(r'\\draline\{SI', line)
        if lineswith_A:
            t = len(lineswith_A)
            A = A + t
        if lineswith_SS:
            t = len(lineswith_SS)
            SS = SS + t
        if lineswith_IS:
            t = len(lineswith_IS)
            IS = IS + t
        if lineswith_CS:
            t = len(lineswith_CS)
            CS = CS + t
        if lineswith_OS:
            t = len(lineswith_OS)
            OS = OS + t
        if lineswith_TS:
            t = len(lineswith_TS)
            TS = TS + t
        if lineswithline_TS:
            t = len(lineswithline_TS)
            TS = TS + t
        if lineswith_PRE:
            t = len(lineswith_PRE)
            PRE = PRE + t
        if lineswithline_PRE:
            t = len(lineswithline_PRE)
            PRE = PRE + t
        if lineswith_PO:
            t = len(lineswith_PO)
            PO = PO + t
        if lineswithline_PO:
            t = len(lineswithline_PO)
            PO = PO + t
        if lineswith_O:
            t = len(lineswith_O)
            O = O + t
        if lineswithline_O:
            t = len(lineswithline_O)
            O = O + t
        if lineswith_SI:
            t = len(lineswith_SI)
            SI = SI + t
            
    print theFile  + str(A) + " & " + str(SS) + " & " + str(IS) + " & " + str(CS) + " & " + str(OS) + " & " + str(TS) + " & " + str(PRE) + " & " + str(PO) + " & " + str(O) + " & " + str(SI)
    print "\n"    
    f.close()
    
def givezdrarelationships(theFile):
    initialof = 0
    requires = 0
    allows = 0
    totalises = 0
    uses = 0 
    f = open(theFile, "r")
    for line in f:
        lineswithinitialof = re.findall(r'\\initialof', line)
        lineswithrequires = re.findall(r'\\requires', line)
        lineswithallows = re.findall(r'\\allows', line)
        lineswithtotalises = re.findall(r'\\totalises', line)
        lineswithuses = re.findall(r'\\uses', line)
        if lineswithinitialof:
            t = len(lineswithinitialof)
            initialof = initialof + t
        if lineswithrequires:
            t = len(lineswithrequires)
            requires = requires + t
        if lineswithallows:
            t = len(lineswithallows)
            allows = allows + t
        if lineswithtotalises:
            t = len(lineswithtotalises)
            totalises = totalises + t
        if lineswithuses:
            t = len(lineswithuses)
            uses = uses + t
    print theFile + ": " + str(initialof) + " & " + str(requires) + " & " + str(allows) + " & " + str(totalises) + " & " + str(uses)
    f.close()
    
def numberoflemmas(theFile):
    initialof = 0
    f = open(theFile, "r")
    for line in f:
        lineswithinitialof = re.findall(r'lemma [a-zA-Z\_0-9]+\_L[0-9]+', line)
        if lineswithinitialof:
            t = len(lineswithinitialof)
            initialof = initialof + t
    print theFile + ": " + str(initialof) 
    f.close()
    
def doNumberOfLemmas():
    numberoflemmas("steamboiler/new6.thy")
    numberoflemmas("projectalloc/6.thy")
    numberoflemmas("videoshop/new6.thy")
    numberoflemmas("telephone/6.thy")
    numberoflemmas("clubstate/new6.thy")
    numberoflemmas("zmathlang/zcga/6.thy")
    numberoflemmas("gendb/6.thy")
    numberoflemmas("timetable/new6.thy")
    numberoflemmas("bb/new6.thy")
    numberoflemmas("semiform/5.thy")
    numberoflemmas("clubstate2/new6.thy")
    numberoflemmas("vm/6.thy")
    numberoflemmas("modulereg/new6.thy")
    
def doZCGaInfo():
    giveMeInfo("steamboiler/1.tex")
    giveMeInfo("projectalloc/1.tex")
    giveMeInfo("videoshop/1.tex")
    giveMeInfo("telephone/1n2.tex")
    giveMeInfo("clubstate/1.tex")
    giveMeInfo("zmathlang/zcga/1.tex")
    giveMeInfo("gendb/1.tex")
    giveMeInfo("timetable/1.tex")
    giveMeInfo("bb/1.tex")
    giveMeInfo("semiform/1.tex")
    giveMeInfo("clubstate2/1.tex")
    giveMeInfo("vm/1.tex")
    giveMeInfo("modulereg/1.tex")
    
def doZDRaInstances():
    giveMeInfoForZDRa("steamboiler/2.tex")
    giveMeInfoForZDRa("projectalloc/2.tex")
    giveMeInfoForZDRa("videoshop/2.tex")
    giveMeInfoForZDRa("telephone/1n2.tex")
    giveMeInfoForZDRa("clubstate/2.tex")
    giveMeInfoForZDRa("zmathlang/zcga/2.tex")
    giveMeInfoForZDRa("gendb/2.tex")
    giveMeInfoForZDRa("timetable/2.tex")
    giveMeInfoForZDRa("bb/2.tex")
    giveMeInfoForZDRa("semiform/1n2.tex")
    giveMeInfoForZDRa("clubstate2/2.tex")
    giveMeInfoForZDRa("vm/2.tex")
    giveMeInfoForZDRa("modulereg/2.tex")
    
def doZDRaRelations():
    givezdrarelationships("steamboiler/2.tex")
    givezdrarelationships("projectalloc/2.tex")
    givezdrarelationships("videoshop/2.tex")
    givezdrarelationships("telephone/1n2.tex")
    givezdrarelationships("clubstate/2.tex")
    givezdrarelationships("zmathlang/zcga/2.tex")
    givezdrarelationships("gendb/2.tex")
    givezdrarelationships("timetable/2.tex")
    givezdrarelationships("bb/2.tex")
    givezdrarelationships("semiform/1n2.tex")
    givezdrarelationships("clubstate2/2.tex")
    givezdrarelationships("vm/2.tex")
    givezdrarelationships("modulereg/2.tex")
    
#giveMeInfoForZDRa("videoshop/1n2.tex")
#print "\n"
#givezdrarelationships("videoshop/1n2.tex")
doNumberOfLemmas()