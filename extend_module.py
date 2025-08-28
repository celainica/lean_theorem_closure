import get_code
import os
import subprocess
import json

constants = []
extend_root_constants = []
constant_dep = {}
extend_constants = []


def get_constants(file_path):        
    constants = []
    with open(file_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        if d["valueReferences"] is not None:
            for const in d["valueReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constants:
                    constants.append(constant_name)
        if d["typeReferences"] is not None:
            for const in d["typeReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constants:
                    constants.append(constant_name)
        c = d['name']
        constant_name = c[0]
        for i in range(1,len(c)):
            constant_name = constant_name + '.' + str(c[i])
        if constant_name not in constants:
            constants.append(constant_name)
    return constants

def get_module(const,module):      
    file_path = "./tmp/"+ module + ".sym.json"
    with open(file_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        valuemod = d["valueModules"][0]
        flag = False
        for c in valuemod:
            if c.endswith(const)and (c==const or c[-(len(const))-1]=='.'):
                flag = True
                break
        if flag and valuemod[c][0]!=None:
            mod = valuemod[c][0]
            mod_name = mod[0]
            for i in range(1,len(mod)):
                mod_name = mod_name + '.' + str(mod[i])
            return mod_name
        
        typemod = d["typeModules"]
        flag = False
        for c in typemod:
            if c.endswith(const)and (c==const or c[-(len(const))-1]=='.'):
                flag = True
                break
        if flag and typemod[c][0]!=None:
            mod = typemod[c][0]
            mod_name = mod[0]
            for i in range(1,len(mod)):
                mod_name = mod_name + '.' + str(mod[i])
            return mod_name

def module_to_file(module,parent):   
    if module==main_module:
        file_path = "./"+main_module+".lean"
        return file_path    
    sym_path = "./tmp/"+ parent + ".sym.json"
    with open(sym_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        for const in d["valueModules"][0]:
            m = d["valueModules"][0][const][0]
            if m == None: continue
            module_name = m[0]
            for i in range(1,len(m)):
                module_name = module_name + '.' + str(m[i])
            if module_name==module:
                file_path = d["valueModules"][0][const][1]
                return file_path
            
        for const in d["typeModules"]:
            m = d["typeModules"][const][0]
            if m == None: continue
            module_name = m[0]
            for i in range(1,len(m)):
                module_name = module_name + '.' + str(m[i])
            if module_name==module:
                file_path = d["typeModules"][0][const][1]
                return file_path

def run_jixia(file_path, module_name): 
    if not os.path.isfile("./tmp/tmp." + module_name + ".lean"):
        with open(file_path, "r", encoding='utf-8') as source_file:
            with open("./tmp/tmp."+ module_name + ".lean" , "w", encoding='utf-8') as target_file:
                for line in source_file.readlines():
                    target_file.write(line)
    
    initial = "lake env lean -o ./"+ module_name + ".olean ./tmp/tmp."+ module_name +".lean"
    if not os.path.isfile("./" + module_name +".olean"):
        print("running：",initial)
        subprocess.run(initial)
    run_flag = False
    if not os.path.isfile("./tmp/" + module_name + ".sym.json"):run_flag = True
    if not os.path.isfile("./tmp/" + module_name + ".decl.json"):run_flag = True
    command = "lake env ./.lake/build/bin/jixia -i -d ./tmp/"+ module_name +".decl.json -s ./tmp/"+module_name+".sym.json "+file_path
    if run_flag: subprocess.run(command)  

def get_constant_dep(file_path):
    global constant_dep
    extend_module_constants = []
    with open(file_path, 'r', encoding='utf-8') as f:
        sym = json.load(f)
    for d in sym:
        c = d['name']
        const = c[0]
        for i in range(1,len(c)):
            const = const + '.' + str(c[i])
        extend_module_constants.append(const)
    for d in sym:
        c = d['name']
        parent_const = c[0]
        for i in range(1,len(c)):
            parent_const = parent_const + '.' + str(c[i])
        
        constant_dep[parent_const] = []
        if d["valueReferences"] is not None:
            for const in d["valueReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constant_dep[parent_const] and constant_name in extend_module_constants:
                    constant_dep[parent_const].append(constant_name)
        if d["typeReferences"] is not None:
            for const in d["typeReferences"]:
                if len(const)==0: continue
                constant_name = const[0]
                for i in range(1,len(const)):
                    constant_name = constant_name + '.' + str(const[i])
                if constant_name not in constant_dep[parent_const] and constant_name in extend_module_constants:
                    constant_dep[parent_const].append(constant_name)

def get_extended_constants(const):
    global extend_constants
    if not const in extend_constants:
        extend_constants.append(const)
        for child in constant_dep[const]:
            get_extended_constants(child)

def sort_constants():
    global extend_constants
    sort_constants = {}
    with open(extend_module_path, 'r', encoding='utf-8') as source:
        codes = source.readlines()
    for constant in extend_constants:
        line = 10000
        pure_constant = constant.split('.')[-1]
        for l in range(0,len(codes)):
            if (" "+pure_constant+" ") in codes[l] or (" "+pure_constant+"\n") in codes[l]:
                if "def" not in codes[l] and "theorem" not in codes[l] and "class" not in codes[l] and "let" not in codes[l]:
                    if "struct" not in codes[l] and "lemma" not in codes[l]:continue
                line = l
                break
        sort_constants[line]=constant
    extend_constants = []
    for ll in sorted(sort_constants):
        extend_constants.append(sort_constants[ll])
    
    

if __name__=="__main__":
    theorem = ""
    main_module = "tes"
    extend_module = "Mathlib.Algebra.Polynomial.Derivative"
    
    main_path = "./"+main_module+".lean"
    main_sym_path = "./tmp/"+main_module+".sym.json"
    run_jixia(main_path,main_module)
    constants = get_constants(main_sym_path)
    count = 0
    for const in constants:
        m = get_module(const,main_module)               #TO-DO add typemodules
        if m == None: continue
        print(const,m)
        if extend_module in m:
            count = count + 1
            print("我佛",const)
            extend_root_constants.append(const)
    #print(extend_root_constants)
    extend_module_path = module_to_file(extend_module,main_module)
    run_jixia(extend_module_path,extend_module)
    extend_sym_path = "./tmp/"+extend_module+".sym.json"
    get_constant_dep(extend_sym_path)
    print("白眉姬鹟",extend_root_constants)
    for root in extend_root_constants:
        get_extended_constants(root)
    print("黄玫姬鹟",extend_constants)
    sort_constants()      
    print("呱呱",extend_constants)
    
    
    
    with open("./sketch.lean", 'w', encoding='utf-8') as target:
        print("import Mathlib\n",file = target)
    for const in extend_constants:
        pure_const = const.split('.')[-1]
        print("\n",pure_const)
        get_code.get_code(pure_const,extend_module_path)
        
    with open("./sketch.lean", 'a', encoding='utf-8') as target:
        target.write("section\n")
    with open(main_path, 'r', encoding='utf-8') as source:
        content = source.readlines()            
    with open("./sketch.lean", 'a', encoding='utf-8') as target:
        target.write(''.join(content[1:]))
    with open("./sketch.lean", 'a', encoding='utf-8') as target:
        target.write("\nend")
        
    with open('./sketch.lean', 'r', encoding='utf-8') as file:
        sketch = file.read()
    for const in extend_constants:
        pure_const = const.split('.')[-1]
        sketch = sketch.replace(pure_const,pure_const+"_tmp")
    with open("./sketch.lean", 'w', encoding='utf-8') as target:
        target.write(sketch)