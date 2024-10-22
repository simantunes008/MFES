from z3 import *

# ! Exercise 1
Survey, License, ABTesting, Statistics, QA, AdvancedLicense, BasicLicense, BasicQA, MultimediaQA = Bools('Survey License ABTesting Statistics QA AdvancedLicense BasicLicense BasicQA MultimediaQA')
features = [Survey, License, ABTesting, Statistics, QA, AdvancedLicense, BasicLicense, BasicQA, MultimediaQA]

s = Solver()

# Survey is a root feature
s.add(Survey)
# License is a mandatory sub-feature of Survey
s.add(License == Survey)
# ABTesting is an optional sub-feature of Survey
s.add(Implies(ABTesting, Survey))
# Statistics is an optional sub-feature of Survey
s.add(Implies(Statistics, Survey))
# QA is a mandatory sub-feature of Survey
s.add(QA == Survey)
# AdvancedLicense and BasicLicense are xor sub-features of License
s.add(Or(AdvancedLicense, BasicLicense) == License)
s.add(Not(And(AdvancedLicense, BasicLicense)))
# BasicQA and MultimediaQA are or sub-features of QA
s.add(Or(BasicQA, MultimediaQA) == QA)
# ABTesting excludes BasicLicense
s.add(Not(And(ABTesting, BasicLicense)))
# ABTesting requires Statistics
s.add(Implies(ABTesting, Statistics))
# BasicLicense excludes MultimediaQA
s.add(Not(And(BasicLicense, MultimediaQA)))

if s.check() == sat:
    print("Feature model is non void")
else:
    print("Feature model is void")

# ! Exercise 2
s.push()
i = 0
while s.check() == sat:
    i += 1
    m = s.model()
    p = []
    for f in features:
        if is_true(m[f]):
            p.append(f)
        else:
            p.append(Not(f))
    s.add(Not(And(p)))
print("Number of variants: ", i)
s.pop()

# ! Exercise 3
for f in features:
    s.push()
    s.add(Not(f))
    if s.check() != sat:
        print(f, "is a core feature")
    s.pop()

# ! Exercise 4
for f in features:
    s.push()
    s.add(f)
    if s.check() != sat:
        print(f, "is a dead feature")
    s.pop()
