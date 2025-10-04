# ======================================================
# inferencia.py - CNF + Unificación + Refutación + Registro en pantalla y archivo
# ======================================================

# --------------------------
# UTILIDADES BÁSICAS
# --------------------------
def _strip_outer_parens(s):
    s = s.strip()
    if not s.startswith("(") or not s.endswith(")"):
        return s
    depth = 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if depth == 0 and i < len(s) - 1:
            return s
    return s[1:-1].strip()

def _split_outside(expr, sep):
    parts, depth, i0 = [], 0, 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif depth == 0 and expr.startswith(sep, i):
            parts.append(expr[i0:i].strip())
            i0 = i + len(sep)
        i += 1
    parts.append(expr[i0:].strip())
    return parts

# --------------------------
# PUNTO 2: UNIFICACIÓN
# --------------------------
def reemplazar(diccionario: {}, original: [str], copias):
    if len(diccionario) == 0:
        if not any(c == original for c in copias):
            copias.append(original)
    for clave in diccionario:
        for reemplazo in diccionario[clave]:
            c_cpy = []
            for c in original:
                c_cpy.append(c.replace(clave, reemplazo))
            new_dic = diccionario.copy()
            new_dic.pop(clave)
            reemplazar(new_dic, c_cpy, copias)
        return

def unificacion(clausula1: [str], clausula2: [str]):
    reemplazos = {}
    copias = []
    for c1 in clausula1:
        for c2 in clausula2:
            splt1 = c1.replace(")", "").replace("-", "").split("(", 1)
            splt2 = c2.replace(")", "").replace("-", "").split("(", 1)
            pred1 = splt1[0]
            pred2 = splt2[0]
            if pred1 == pred2:
                if len(splt1[1].split(",")) == 1:
                    v1 = splt1[1]
                    v2 = splt2[1]
                    if v1[0].isupper() and not v2[0].isupper():
                        if v2 not in reemplazos:
                            reemplazos[v2] = []
                        reemplazos[v2].append(v1)
                    elif v2[0].isupper() and not v1[0].isupper():
                        if v1 not in reemplazos:
                            reemplazos[v1] = []
                        reemplazos[v1].append(v2)
                else:
                    v11 = splt1[1].split(",")[0]
                    v12 = splt1[1].split(",")[1]
                    v21 = splt2[1].split(",")[0]
                    v22 = splt2[1].split(",")[1]
                    if v11[0].isupper() and v12[0].isupper() and (not v21[0].isupper()) and (not v22[0].isupper()):
                        copias.append([c.replace(v21, v11).replace(v22, v12) for c in clausula1] +
                                      [c.replace(v21, v11).replace(v22, v12) for c in clausula2])
                    elif (not v11[0].isupper()) and (not v12[0].isupper()) and v21[0].isupper() and v22[0].isupper():
                        copias.append([c.replace(v11, v21).replace(v12, v22) for c in clausula1] +
                                      [c.replace(v11, v21).replace(v12, v22) for c in clausula2])
                    elif v11[0].isupper() and (not v21[0].isupper()) and (not v22[0].isupper()):
                        if v21 not in reemplazos:
                            reemplazos[v21] = []
                        reemplazos[v21].append(v11)
                    elif (not v11[0].isupper()) and (not v12[0].isupper()) and v21[0].isupper() and v22[0].isupper():
                        if v11 not in reemplazos:
                            reemplazos[v11] = []
                        reemplazos[v11].append(v21)
                    
                        if v12 not in reemplazos:
                            reemplazos[v12] = []
                        reemplazos[v12].append(v22)
                    elif v12[0].isupper() and (not v21[0].isupper()) and (not v22[0].isupper()):
                        if v22 not in reemplazos:
                            reemplazos[v22] = []
                        reemplazos[v22].append(v12)
                    elif (not v11[0].isupper()) and (not v12[0].isupper()) and v22[0].isupper():
                        if v12 not in reemplazos:
                            reemplazos[v12] = []
                        reemplazos[v12].append(v22)

    reemplazar(reemplazos, clausula1 + clausula2, copias)
    return copias
# --------------------------
# PUNTO 1: CONVERSIÓN A FNC
# --------------------------
def a_fnc(expr):
    expr = expr.replace("∀x", "").replace("∀y", "").replace("∃x", "").replace("∃y", "")
    expr = expr.strip()

    while "⇔" in expr:
        izq, der = expr.split("⇔")
        expr = f"(({izq})→({der})) ∧ (({der})→({izq}))"

    while "→" in expr:
        left, right = expr.split("→", 1)
        left = _strip_outer_parens(left)
        right = _strip_outer_parens(right)
        partes = _split_outside(left, "∧")
        negadas = [f"¬{p.strip()}" for p in partes if p.strip() != ""]
        expr = "(" + " ∨ ".join(negadas + [right]) + ")"

    while "¬¬" in expr:
        expr = expr.replace("¬¬", "")

    if "¬(" in expr:
        i = expr.index("¬(")
        j = i + 2
        depth = 1
        while j < len(expr) and depth > 0:
            if expr[j] == "(":
                depth += 1
            elif expr[j] == ")":
                depth -= 1
            j += 1
        dentro = expr[i+2:j-1]
        if "∧" in dentro:
            partes = _split_outside(dentro, "∧")
            expr = "(" + " ∨ ".join(["¬" + p for p in partes]) + ")"
        elif "∨" in dentro:
            partes = _split_outside(dentro, "∨")
            expr = "(" + " ∧ ".join(["¬" + p for p in partes]) + ")"

    conj = _split_outside(expr, "∧")
    clausulas = []
    for c in conj:
        disy = _split_outside(_strip_outer_parens(c), "∨")
        clausulas.append([d.strip() for d in disy])
    return clausulas

def forma_normal_conjuntiva(axiomas):
    cnf = []
    for ax in axiomas:
        cnf += a_fnc(ax)
    return cnf


# --------------------------
# UNIFICACIÓN
# --------------------------
def _is_var(t):
    return len(t) > 0 and t[0].islower()

def _parse_lit(lit):
    lit = lit.strip()
    neg = lit.startswith("¬")
    if neg:
        lit = lit[1:].strip()
    if "(" in lit:
        pred, args = lit.split("(", 1)
        args = args[:-1]
        args = [a.strip() for a in args.split(",") if a.strip() != ""]
    else:
        pred, args = lit, []
    return neg, pred, args

def _unify_terms(a, b, theta):
    if a in theta: a = theta[a]
    if b in theta: b = theta[b]
    if a == b:
        return True
    if _is_var(a):
        theta[a] = b
        return True
    if _is_var(b):
        theta[b] = a
        return True
    return False

def _unify_lits(li, lj):
    n1, p1, a1 = _parse_lit(li)
    n2, p2, a2 = _parse_lit(lj)
    if p1 != p2 or n1 == n2 or len(a1) != len(a2):
        return None
    theta = {}
    for x, y in zip(a1, a2):
        if not _unify_terms(x, y, theta):
            return None
    return theta

def _apply_sigma(lit, theta):
    neg = lit.startswith("¬")
    if neg: lit = lit[1:]
    if "(" in lit:
        pred, args = lit.split("(", 1)
        args = args[:-1]
        args = [a.strip() for a in args.split(",") if a.strip() != ""]
        new_args = [theta[a] if a in theta else a for a in args]
        lit = f"{pred}({','.join(new_args)})"
    return ("¬" if neg else "") + lit

# --------------------------
# PUNTO 3: RESOLUCIÓN POR REFUTACIÓN
# --------------------------
def _resolve(C1, C2):
    resolvents = []
    for l1 in C1:
        for l2 in C2:
            theta = _unify_lits(l1, l2)
            if theta:
                new_clause = []
                for x in C1:
                    if x != l1:
                        new_clause.append(_apply_sigma(x, theta))
                for x in C2:
                    if x != l2:
                        lit = _apply_sigma(x, theta)
                        if lit not in new_clause:
                            new_clause.append(lit)
                resolvents.append((l1, l2, theta, new_clause))
    return resolvents

def refutacion(axiomas, sentencia, archivo_salida="clausulas.txt"):
    axiomas = list(axiomas)
    axiomas.append("¬" + sentencia)
    clausulas = forma_normal_conjuntiva(axiomas)

    with open(archivo_salida, "w", encoding="utf-8") as f:
        print("\n===== CLÁUSULAS INICIALES (FNC) =====")
        f.write("===== CLÁUSULAS INICIALES (FNC) =====\n")
        for i, c in enumerate(clausulas):
            print(f"C{i+1}: {c}")
            f.write(f"C{i+1}: {c}\n")

        nuevas = clausulas[:]
        paso = 1
        f.write("\n===== PASOS DE RESOLUCIÓN =====\n")
        print("\n===== PASOS DE RESOLUCIÓN =====")
        while True:
            pares = [(clausulas[i], clausulas[j]) for i in range(len(clausulas)) for j in range(i+1, len(clausulas))]
            agregadas = []
            for (C1, C2) in pares:
                resolvents = _resolve(C1, C2)
                for (l1, l2, theta, R) in resolvents:
                    info = (
                        f"\nPaso {paso}: Resolver {C1} y {C2}\n"
                        f"  Literales complementarios: {l1} ⟂ {l2}\n"
                        f"  Sustitución: {theta}\n"
                        f"  Resultado: {R}\n"
                    )
                    print(info)
                    f.write(info)
                    paso += 1
                    if R == []:
                        fin = "\n>>> Se obtuvo la cláusula vacía. REFUTACIÓN COMPLETA\n"
                        print(fin)
                        f.write(fin)
                        return True
                    if R not in nuevas:
                        nuevas.append(R)
                        agregadas.append(R)
            if not agregadas:
                fin = "\n>>> No se pudo derivar contradicción\n"
                print(fin)
                f.write(fin)
                return False
            clausulas = nuevas

# --------------------------
# PRUEBAS
# --------------------------
if __name__ == "__main__":
    axiomas = [
    "∀x ∀y (Igual(x,y) → Igual(y,x))", 
    "∀x ∀y ∀z ((Igual(x,y) ∧ Igual(y,z)) → Igual(x,z))",
    "Igual(a,b)",
    "Igual(b,c)",
    ]

    sentencia = "Igual(a, c)"

    print("\nCONVERSIÓN A FNC")
    for ax in axiomas:
        print("Axioma:", ax)
        print("FNC:", a_fnc(ax))
        print()
    
    # Unificacion
    print("UNIFICACIÓN")
    # Ejemplo 1: variable v.s constante
    c1 = ["Padre(x, Juan)"]
    c2 = ["Padre(Pedro, Juan)"]
    print("Ejemplo 1: ", unificacion(c1, c2))
    # Ejemplo 2: dos variables v.s dos constantes
    c1 = ["Amigo(x,y)"]
    c2 = ["Amigo(Ana, Luis)"]
    print("Ejemplo 2: ", unificacion(c1, c2))


    print("\nRESOLUCIÓN POR REFUTACIÓN")
    resultado = refutacion(axiomas, sentencia, "clausulas.txt")

    print("\n===== RESULTADO FINAL =====")
    if resultado:
        print(f"La sentencia '{sentencia}' se puede probar por refutación\n")
    else:
        print(f"La sentencia '{sentencia}' NO se puede probar\n")
