from z3 import *

EShop,Catalogue,Payment,Security,GUI,Banners,Offers,Info,Search,BankDraft,CreditCard,High,Medium,PC,Mobile,Info,Basic,Advanced,Visa,AmericanExpress,Image,Description,Price = Bools('EShop Catalogue Payment Security GUI Banners Offers Info Search BankDraft CreditCard High Medium PC Mobile Info Basic Advanced Visa AmericanExpress Image Description Price')
features = [EShop, Catalogue, Payment, Security, GUI, Banners, Offers, Info, Search, BankDraft, CreditCard, High, Medium, PC, Mobile, Info, Basic, Advanced, Visa, AmericanExpress, Image, Description, Price]

s = Solver()

# ! Nível 1
s.add(EShop)

# ! Nível 2
s.add(Catalogue == EShop)
s.add(Payment == EShop)
s.add(Implies(Security,EShop))
s.add(GUI == EShop)
s.add(Implies(Banners,EShop))

# ! Nível 3
s.add(Implies(Offers,Catalogue))
s.add(Info == Catalogue)
s.add(Implies(Search,Catalogue))

s.add(Or(BankDraft,CreditCard) == Payment)
s.add(Implies(CreditCard,High))

s.add(Or(High,Medium) == Security)
s.add(Not(And(High,Medium)))

s.add(Or(PC,Mobile) == GUI)
s.add(Not(And(Mobile,Banners)))

# ! Nível 4
s.add(Or(Image,Description,Price) == Info)
s.add(Or(Basic,Advanced) == Search)
s.add(Or(Visa,AmericanExpress) == CreditCard)

# ? Pergunta 1
max = 0
for i in features:
    for j in features:
        s.push()
        s.add(Implies(i,j))
        
        counter = 0
        for f in features:
            s.push()
            s.add(f)
            if s.check() != sat:
                counter += 1
            s.pop()
        
        if counter > max:
            max = counter
        s.pop()
print("Maximum number of dead features:", max)

# ? Pergunta 2
s.push()
s.add(Search == Catalogue)
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
print("Number of variants:", i)
s.pop()
