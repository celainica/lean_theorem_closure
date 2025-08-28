import re

codes = []
interested = []
section = []                #stack detecting sections


def find_attr(ll):
    global interested
    
    while True:
        interested[ll]=True
        if "@" in codes[ll] or "/-" in codes[ll] or codes[ll]=="\n":
            return
        ll = ll-1
        if ll==0 : break

def find_local_def(ll):
    global interested
    
    sect = []
    
    for x in range(0,ll):
        if "end" in codes[x]:
            pattern = r'end\s+(\w+)\s'
            s = re.search(pattern, codes[x])
            sn=""
            if s and codes[x][0:3]=="end": 
                sn = s.group(1)
            else: 
                if codes[x]=="end\n":sn = "no_name" 
            if sect!=[]and sn == sect[len(sect)-1][0]:
                sect.pop()
        if "section" in codes[x]:
            pattern = r'section\s+(\w+)\s'
            s = re.search(pattern, codes[x])
            if s: sect.append([s.group(1),x])
            else: sect.append(["no_name",x])
        if "namespace" in codes[x]:
            pattern = r'namespace\s+(\w+)\s'
            s = re.search(pattern, codes[x])
            if s: sect.append([s.group(1),x])
        
        flag = True
        for y in range(0,len(sect)):
            if sect[y]!=section[y]:
                flag = False
                break
        if not flag:continue
        
        if "variable" in codes[x] or ("open" in codes[x] and "in" not in codes[x]) or "universe" in codes[x]:
            interested[x] = True

def get_code(constant,file_path):
    global codes
    global interested
    global section
    #file_path = ".lake/packages/mathlib/Mathlib/Algebra/Polynomial/FieldDivision.lean"
    with open(file_path, 'r', encoding='utf-8') as f:
        codes = f.readlines()
    
    #print(codes)
        
    interested = []
    section = []
    for l in range(0,len(codes)):interested.append(False)
        
    found = False
    sectionflag = False
    
    for l in range(0,len(codes)):
        if "end" in codes[l]:
            pattern = r'end\s+(\w+)\s'
            sec = re.search(pattern, codes[l])
            section_name=""
            if sec and codes[l][0:3]=="end": 
                section_name = sec.group(1)
            else: 
                if codes[l]=="end\n":section_name = "no_name"
                
            if section!=[]and section_name == section[len(section)-1][0]:
                if sectionflag:
                    interested[section[len(section)-1][1]] = True
                    interested[l] = True
                    codes[section[len(section)-1][1]] += "\n"
                    codes[l] += "\n"
                section.pop()
                if section==[]:sectionflag = False
        if "section" in codes[l] and not found:
            pattern = r'section\s+(\w+)\s'
            sec = re.search(pattern, codes[l])
            if sec: section.append([sec.group(1),l])
            else: section.append(["no_name",l])
        if "namespace" in codes[l] and not found:
            pattern = r'namespace\s+(\w+)\s'
            sec = re.search(pattern, codes[l])
            if sec: section.append([sec.group(1),l])
            
        if not found:
            if (" "+constant+" ") not in codes[l] and (" "+constant+"\n") not in codes[l]: continue
            if "def" not in codes[l] and "theorem" not in codes[l] and "class" not in codes[l] and "let" not in codes[l]:
                if "struct" not in codes[l] and "lemma" not in codes[l]:continue
            found = True
            if section!=[]:sectionflag = True
            find_attr(l)
            for x in range(l,len(codes)):
                interested[x] = True
                if x>l and codes[x][0:2]!="  ": break
            find_local_def(l)

                
    for l in range(0,len(codes)):
        if interested[l]:
            #print(l,"\n",codes[l])
            with open("./sketch.lean", 'a', encoding='utf-8')as f:
                print(codes[l],end = "",file = f)
                

                
if __name__=="__main__":
    get_code("isRoot_iterate_derivative_of_lt_rootMultiplicity","")