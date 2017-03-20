from __future__ import division
import sys,re,os

# Written by Timothy Herchen, 12/19/16.
# The following procedures parametrize (parametize?) many equations the user gives in a GUI input.

# Mac only! 

exprwidth = 100
# Operating system detected.

keywords = ["\\sqrt","\\tan",\
            "\\arctan",\
            "\\tanh",\
            "\\arctanh","\\cot",\
            "\\arccot",\
            "\\arccoth",\
            "\\total","\\quantile",\
            "\\stdev","\\stdevp",\
            "\\int","\\left","\\right"]

def spreadt(expr):
    """spreadt(expr) takes a string equation and replaces all variable t's with a larger range."""
    for keyword in keywords:
        # "protect" certain keywords
        expr = expr.replace(keyword,"fx0@idfier%s"%keyword.replace("t","q"))
    expr = expr.replace("t","(%st-%s)"%(exprwidth,exprwidth/2))
    # replace all t's with a larger range
    for keyword in keywords:
        # undo keyword protection
        expr = expr.replace("fx0@idfier%s"%(keyword.replace("t","q")),keyword)
    return expr

def anglespreadt(expr):
    """anglespreadt(expr) takes a string equation and replaces all variable t's with a larger angle range."""
    # This function is unused and WIP.
    return expr.replace("t","(6.29t)")

def iterspreadt(exprlist):
    """iterspreadt(exprlist) takes a list of equations and applies spreadt(expr) to each equation."""
    return [spreadt(expr) for expr in exprlist]

def yantecedent(expr):
    """Formulate equations of the form y=f(x)."""
    return iterspreadt(["t",expr[1].replace("x","t")])

def xantecedent(expr):
    """Formulate equations of the form x=f(y)."""
    return iterspreadt([expr[1].replace("y","t"),"t"])

def latexform(expr):
    """Turn equations into Desmos-readable form."""
    return expr.replace("\\left(","(").replace("\\right)",")")\
           .replace("(","\\left(").replace(")","\\right)")

def parametric(expr):
    """Turn most equations into parametric form."""
    return ("\\left(%s,%s\\right)" % (latexform(expr[0]),latexform(expr[1])))\
           .replace("\\left\\left","\\left").replace("\\right\\right","\\right")

def extractbounds(expr):
    """Returns all bounded inequalities from the expression as an iterator."""
    inbound = 0 # Tracks depth of {...} markers
    lasti = 0 # Tracks last { seen's position
    for i in xrange(len(expr)):
        if (inbound != 0 and expr[i] == "{"):
            inbound += 1
        if (inbound == 0 and expr[i] == "{"):
            lasti = i
            inbound += 1
        if (expr[i] == "}"):
            # This section is run when the end of a {...} string is found.
            inbound -= 1
            if (inbound == 0 and ("<" in expr[lasti+1:i] or ">" in expr[lasti+1:i])):
                # If this section has depth 0 and contains an inequality mark, keep track of it.
                yield expr[lasti+1:i]

def copy():
    """This function copies the outputstream to the clipboard."""
    global outputstream,master
    master.clipboard_clear()
    master.clipboard_append(outputstream.get(0.0,END))
        
    # Note: Mac-supported only, might work on Windows.
    return

def parametize(inputequation):
    """This is the central logic of the parametizer. It will parametize many different types of equations."""

    inputequation = inputequation.replace("\n","")
    
    # If the input equation has no = sign, assume it is of the form y=f(x) as Desmos does.
    if (not ("=" in inputequation) and "x" in inputequation):
        stringequation = "y=" + inputequation
    else:
        stringequation = inputequation

    # "de-Desmosify" parentheses; will be added back later in latexform(expr).
    stringequation = stringequation.replace("\\left(","(")\
                     .replace("\\right)",")")\
                     .replace("\\left\\{","{")\
                     .replace("\\right\\}","}")

    # boundregex = re.compile("\{.+\}")
    
    bounds = list(extractbounds(stringequation)) # Bounds of stringequation.
    mbounds = []
    cbounds = ""
    
    # The following code removes the inequalities from the stringequation.
    for bound in bounds:
        stringequation = stringequation.replace("{%s}" % bound,"")\
                         .replace("\\{%s\\}" % bound,"")\
                         .replace("\\left{%s\\right}" % bound,"")\
                         .replace("\\left{%s\\right}" % bound,"")

    # This loop moves the inequalities "in order" to mbounds.
    for bound in bounds:
        if (len(bound.split(">"))>1):
            # Reached if the bound has at least one > operator
            boundsplit = bound.split(">")
            if (len(boundsplit)==2):
                # If of the form a > b, append [b,a]
                mbounds.append(boundsplit[::-1])
            if (len(boundsplit)==3):
                # If of the form a > b > c, append [b,a] and [c,b]
                mbounds.append([boundsplit[1],boundsplit[0]])
                mbounds.append([boundsplit[2],boundsplit[1]])
        if (len(bound.split("<"))>1):
            # Reached if the bound has at least one < operator
            boundsplit = bound.split("<")
            if (len(boundsplit)==2):
                # If of the form a < b, append [a,b]
                mbounds.append(boundsplit)
            if (len(boundsplit)==3):
                # If of the form a < b < c, append [a,b] and [b,c]
                mbounds.append([boundsplit[0],boundsplit[1]])
                mbounds.append([boundsplit[1],boundsplit[2]])

    # Turns inequalities in mbounds into a single expression that will work in the eventual parametric form.
    for mbound in mbounds:
        cbounds = cbounds + "\\left(\\operatorname{sign}\\left(\\left(%s\\right)-\\left(%s\\right)\\right)-1\\right)"\
                  % (mbound[0],mbound[1])

    # cbounds is now effectively a product of sign functions. In the end equation, this product will be 0 when an original inequality does not hold, so it will be made undefined then.

    equation = stringequation.split("=")

    # equation[0] = equation[0].replace(" ","")
    # equation[1] = equation[1].replace(" ","")

    # equation holds a split form of stringequation across the = sign.

    if (len(equation) != 2):
        raise TypeError

    if (equation[0] == "y"):
        # Reached when equation is of the form y=f(x).
        mq = yantecedent(equation)
        # This line adds the inequalities from cbounds into the expression. It will be seen in every if statement.
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)
        
    if (equation[0] == "x"):
        # Reached when the equation is of the form x=f(y).
        mq = xantecedent(equation)
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    # Here come the harder equations to deal with.

    lhsysubtractregex = re.compile("y-[a-xzA-Z0-9_\\^]+")
    lhsyadditionregex = re.compile("y\+[a-xzA-Z0-9_\\^]+")
    lhsxsubtractregex = re.compile("x-[a-wyzA-Z0-9_\\^]+")
    lhsxadditionregex = re.compile("x\+[a-wyzA-Z0-9_\\^]+")

    if (re.match(lhsysubtractregex,equation[0])):
        # Reached when equation is of the form y-c=f(x)
        equation[1] = equation[1] + "+\\left(" + equation[0][2:]+"\\right)"
        equation[0] = 0
        mq = yantecedent(equation)
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(lhsyadditionregex,equation[0])):
        # Reached when equation is of the form y+c=f(x)
        equation[1] = equation[1] + "-\\left(" + equation[0][2:] + "\\right)"
        equation[0] = 0
        mq = yantecedent(equation)
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)
    
    if (re.match(lhsxsubtractregex,equation[0])):
        # Reached when equation is of the form x-c=f(y)
        equation[1] = equation[1] + "+\\left(" + equation[0][2:]+"\\right)"
        equation[0] = 0
        mq = xantecedent(equation)
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(lhsxadditionregex,equation[0])):
        # Reached when equation is of the form x+c=f(y)
        equation[1] = equation[1] + "-\\left(" + equation[0][2:] + "\\right)"
        equation[0] = 0
        mq = xantecedent(equation)
        mq[1] = mq[1] + (( "+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    # The rest of the logic here is for circles.

    simplecircle = re.compile("\(?x\)?\^\{?2\}?\+\(?y\)?\^\{?2\}?")
    xsimplecircle = re.compile("\(?x\)?\^\{?2\}?\+\(y(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?2\}?")
    ysimplecircle = re.compile("\(x(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?2\}?\+\(?y\)?\^\{?2\}?")
    complexcircle = re.compile("\(x(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?2\}?\+\(y(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?2\}?")

    # Not the prettiest regular expressions ever, but they get the job done....

    if (re.match(simplecircle,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form x^2+y^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{%s}\\cos \\left(2\pi t\\right)" % equation[1]
        mq[1] = "\\sqrt{%s}\\sin \\left(2\pi t\\right)" % equation[1]
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(xsimplecircle,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form x^2+(y-k)^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{%s}\\cos \\left(2\pi t\\right)" % equation[1]
        mq[1] = "\\sqrt{%s}\\sin \\left(2\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(xsimplecircle,equation[0]).groups()[0])
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(ysimplecircle,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form (x-h)^2+y^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{%s}\\cos \\left(2\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(ysimplecircle,equation[0]).groups()[0])
        mq[1] = "\\sqrt{%s}\\sin \\left(2\pi t\\right)" % equation[1]
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(complexcircle,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form (x-h)^2+(y-k)^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{%s}\\cos \\left(2\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(complexcircle,equation[0]).groups()[0])
        mq[1] = "\\sqrt{%s}\\sin \\left(2\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(complexcircle,equation[0]).groups()[1])
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    # Eggs

    simpleegg = re.compile("\(?x\)?\^\{?4\}?\+\(?y\)?\^\{?4\}?")
    xsimpleegg = re.compile("\(?x\)?\^\{?4\}?\+\(y(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?4\}?")
    ysimpleegg = re.compile("\(x(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?4\}?\+\(?y\)?\^\{?4\}?")
    complexegg = re.compile("\(x(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?4\}?\+\(y(-?\+?[\d\.\\\{\}a-wzA-Z]+)\)\^\{?4\}?")

    if (re.match(simpleegg,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form x^2+y^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\cos 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\cos 2\\pi t\\right)" % equation[1]
        mq[1] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\sin 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\sin 2\\pi t\\right)" % equation[1]
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(xsimpleegg,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form x^2+(y-k)^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\cos 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\cos 2\\pi t\\right)" % equation[1]
        mq[1] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\sin 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\sin 2\\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(xsimpleegg,equation[0]).groups()[0])
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(ysimpleegg,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form (x-h)^2+y^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\cos 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\cos 2\\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(ysimpleegg,equation[0]).groups()[0])
        mq[1] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\sin 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\sin 2\\pi t\\right)" % equation[1]
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    if (re.match(complexegg,equation[0]) and not ("x" in equation[1] or "y" in equation[1])):
        # Reached if equation is of the form (x-h)^2+(y-k)^2=c^2
        mq = ["",""]
        mq[0] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\cos 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\cos 2\\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(complexegg,equation[0]).groups()[0])
        mq[1] = "\\sqrt{\\sqrt{%s}}\\sqrt{\\left|\\sin 2\\pi t\\right|}\\cdot \\operatorname{sign}\\left(\\sin 2\\pi t\\right)-\\left(%s\\right)" % (equation[1],re.match(xsimpleegg,equation[0]).groups()[1])
        mq[1] = mq[1] + (("+0\\left(%s\\right)^{-1}" % cbounds.replace("x",mq[0]).replace("y",mq[1])) if (cbounds != "") else "")
        return parametric(mq)

    # Ellipses (WIP)
    
    return ""

    # Todo list:

    # Ellipses
    # Equations of the form (x-h)^4+(y-k)^4=c^4
    # Bezier Curves?
    # Elliptic Curves
    # Are lists possible?

while (True):
    n = raw_input("> ")
    print parametize(n)


