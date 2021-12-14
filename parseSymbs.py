def _parse_symbs(self):
    self._iter_lines(self._parse_macro)
# Prvo parsiramo deklaracije oznaka. Npr. "(LOOP)"
    self._iter_lines(self._parse_lab)
# Na kraju parsiramo varijable i reference na oznake te ih pretvaramo u
# konstante. Npr. "@SCREEN" pretvaramo u "@16384" ili "@END" kojemu je
# oznaka "(END)" bila u trecoj liniji pretvaramo u "@3".
    self._n = 16
    self._iter_lines(self._parse_var)

    
def _parse_macro(self, line, m, n):
    if line[0] != "$":
        return line
    
    if (not (line[-1] == ")" or line[-1] == "D")):
        self._flag = False
        self._line = n
        self._errm = "Invalid macro operation."
        return ""
    
    op = line[1:].split("(")[0]
    if op == "MV":
        if len(op[1].split(",")) != 2:
            self._flag = False
            self._line = n
            self._errm = "Invalid macro operation."
            return ""
        a = op[1].split(",")[0]
        b = op[1].split(",")[1]
        return "@" + a + "\n" + "D=M" + "\n" + "@" + b + "\n" + "M=D"
        
    elif op == "SWP":
        if (op[1].split(",")) != 2:
            self._flag = False
            self._line = n
            self._errm = "Invalid macro operation."
            return ""
        a = op[1].split(",")[0]
        b = op[1].split(",")[1]
        return  "@" + a + "\n" + "D=M" + "\n" + "@" + "H" + "\n" + "M=D" + "\n" + "@" + b + "\n" + "D=M" + "\n" + "@" + a \
                + "\n" + "M=D" + "\n" + "@" + "H" + "\n" "D=M" + "\n" + "@" + b + "\n" + "M=D"
        
    elif op == "SUM":
        if len(op[1].split(",")) != 3:
            self._flag = False
            self._line = n
            self._errm = "Invalid macro operation."
            return ""
        a = op[1].split(",")[0]
        b = op[1].split(",")[1]
        c = op[1].split(",")[2]
        return "@" + a + "\n" + "D=M" + "\n" + "@" + b + "\n" + "D=M+D" + "\n" + "@" + c + "\n" + "M=D"   
    else:
        self._flag = False
        self._line = n
        self._errm = "Invalid macro operation."
        return ""
    
# Svaka oznaka mora biti sadrzana unutar oblih zagrada. Npr. "(LOOP)". Svaka
# oznaka koju procitamo treba zapamtiti broj linije u kojoj se nalazi i biti
# izbrisana iz nje. Koristimo dictionary _labels.
def _parse_lab(self, line, m, n):
    if line[0] != "(":
        return line
    l = line[1:].split(")")[0]
    l1 = line[1:].split(")")[1]
    if len(l) == 0 or len(l1) > 0:
        self._flag = False
        self._line = n
        self._errm = "Invalid label."
    else:
        self._labels[l] = str(m)
    return ""

# Svaki poziv na varijablu ili oznaku je oblika "@NAZIV", gdje naziv nije broj.
# Prvo provjeriti oznake ("_labels"), a potom varijable ("_vars"). Varijablama
# dodjeljujemo memorijske adrese pocevsi od 16. Ova funkcija nikad ne vraca
# prazan string!
def _parse_var(self, line, m, n):
    if line[0] != '@' or (line[0] == '@' and line[1:].isdigit()):
        return line
    l = line[1:]
    if l in self._labels.keys():
        return "@" + self._labels[l]
    elif l in self._vars.keys():
        return "@" + self._vars[l]
    else:
        self._vars[l] = str(self._n)
        self._n += 1
        return "@" + str(self._n - 1)

# Inicijalizacija predefiniranih oznaka.
def _init_symbs(self):
    self._labels = {
        "SCREEN" : "16384",
        "KBD" : "24576",
        "SP" : "0",
        "LCL" : "1",
        "ARG" : "2",
        "THIS" : "3",
        "THAT" : "4"
    }
    for i in range(0, 16):
        self._labels["R" + str(i)] = str(i)
