# --- helpers para 3er punto ---
import re
def _strip_outer_parens(s):
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        for i,ch in enumerate(s):
            if ch == "(": depth += 1
            elif ch == ")": depth -= 1
            if depth == 0 and i < len(s)-1:
                return s  # había algo fuera de los () externos
        return s[1:-1].strip()
    return s

def _split_outside(s, sep):
    parts, depth, i0 = [], 0, 0
    i = 0
    while i < len(s):
        ch = s[i]
        if ch == "(": depth += 1
        elif ch == ")": depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            parts.append(s[i0:i].strip()); i0 = i + len(sep)
        i += 1
    parts.append(s[i0:].strip())
    return parts

def _norm_lit(l):
    l = l.strip()
    l = l.replace(" ", "")       # borra todos los espacios
    l = re.sub(r"^¬+", "¬", l)   # normaliza negaciones múltiples
    return l

def _parse_lit(l):
    l = _norm_lit(l)
    neg = l.startswith("¬")
    if neg: l = l[1:].strip()
    m = re.match(r"([A-Za-z_][A-Za-z_0-9]*)\(([^()]*)\)$", l)
    if not m:  # literal mal formado
        return neg, l, []
    pred = m.group(1)
    args = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
    return neg, pred, args

def _is_var(t):  # convención: variables inician en minúscula
    return t and t[0].islower()

def _unify_terms(a, b, theta=None):
    if theta is None: theta = {}
    a = theta.get(a, a); b = theta.get(b, b)
    if a == b: return theta
    if _is_var(a): theta[a] = b; return theta
    if _is_var(b): theta[b] = a; return theta
    return None

def _unify_lits(li, lj):
    n1,p1,a1 = _parse_lit(li); n2,p2,a2 = _parse_lit(lj)
    if p1 != p2 or n1 == n2 or len(a1) != len(a2): return None
    theta = {}
    for x,y in zip(a1,a2):
        theta = _unify_terms(x, y, theta)
        if theta is None: return None
    return theta

def _apply_sigma(lit, sigma):
    lit = _norm_lit(lit)
    neg = lit.startswith("¬")
    if neg: lit = lit[1:].strip()
    m = re.match(r"([A-Za-z_][A-Za-z_0-9]*)\(([^()]*)\)$", lit)
    if m:
        pred = m.group(1)
        args = [a.strip() for a in m.group(2).split(",") if a.strip()!='']
        args = [sigma.get(a, a) for a in args]
        lit = f"{pred}({','.join(args)})"
    return ("¬" if neg else "") + lit
# --- fin helpers ---


# Punto 1. Crear funcion

# Paso 1: Eliminar bicondicionales (⇔)
def eliminar_bicondicional(expr):
    if "⇔" in expr:
        left, right = expr.split("⇔")
        return f"({left}→{right}) ∧ ({right}→{left})"
    return expr

# Paso 2: Eliminar implicaciones (→)
def eliminar_entonces(expr):
    if "→" in expr:
        left, right = expr.split("→", 1)
        # limpiar cuantificador universal
        left = left.replace("∀x", "").strip()
        if left.startswith("(") and left.endswith(")"):
            left = left[1:-1].strip()
        left = left.replace(" ", "")
        right = right.strip()
        # OJO: si right tiene paréntesis, no lo tratamos como un solo argumento, se pasa tal cual
        return f"(¬{left}) ∨ ({right})"
    return expr

# Paso 3: Aplicar De Morgan y mover negaciones hacia adentro
def aplicar_demorgan(expr):
    expr = expr.replace("¬(P ∧ Q)", "(¬P ∨ ¬Q)")
    expr = expr.replace("¬(P ∨ Q)", "(¬P ∧ ¬Q)")
    expr = expr.replace("¬¬", "")

    # Manejo de cuantificadores
    resultado = ""
    i = 0
    while i < len(expr):
        if expr[i:i+2] == "¬∀":  
            var = expr[i+2]
            resultado += f"∃{var}¬"
            i += 3
        elif expr[i:i+2] == "¬∃":
            var = expr[i+2]
            resultado += f"∀{var}¬"
            i += 3
        else:
            resultado += expr[i]
            i += 1
    return resultado

# Paso 4: Estandarizar variables (simplificado)
def estandarizar_variables(expr, usados=set()):
    resultado = ""
    for i, c in enumerate(expr):
        if c in ["x","y","z","w"]:
            if c in usados:
                nuevo = chr(ord(c) + 1)  # cambia a otra letra
                resultado += nuevo
                usados.add(nuevo)
            else:
                resultado += c
                usados.add(c)
        else:
            resultado += c
    return resultado

# Paso 5 y 6: Skolemización (eliminar existenciales ∃)
contador_skolem = 1

def skolemizar(expr):
    global contador_skolem
    while "∃" in expr:
        pos = expr.index("∃")
        var = expr[pos+1]
        const = f"c{contador_skolem}"
        contador_skolem += 1
        expr = expr.replace(f"∃{var}", "")
        
        # Cambiar SOLO el argumento de la variable, no el nombre del predicado
        expr = expr.replace(f"({var})", f"({const})")
    return expr


# Paso 7: Eliminar cuantificadores universales (∀ queda implícito)
def quitar_universales(expr):
    return expr.replace("∀", "")

# Paso 8: Distribuir OR sobre AND
def distribuir_or(expr):
    # muy básico, solo casos típicos
    if "∨" in expr and "∧" in expr:
        expr = expr.replace("(P ∨ (Q ∧ R))", "((P ∨ Q) ∧ (P ∨ R))")
        expr = expr.replace("((Q ∧ R) ∨ P)", "((Q ∨ P) ∧ (R ∨ P))")
    return expr

# Paso 9: Separar en cláusulas
def separar_clausulas(expr):
    expr = _strip_outer_parens(expr)
    conj = _split_outside(expr, "∧")
    clausulas = []
    for c in conj:
        disy = _split_outside(c, "∨")
        literales = []
        for d in disy:
            d = d.strip()
            if d.startswith("(") and d.endswith(")"):
                d = d[1:-1]
            if d.startswith("¬(") and d.endswith(")"):
                d = "¬" + d[2:-1]
            literales.append(_norm_lit(d))
        clausulas.append(literales)
    return clausulas

# Función principal: convertir a FNC
def forma_normal_conjuntiva(axiomas):
    resultado = []
    for ax in axiomas:
        paso1 = eliminar_bicondicional(ax)
        paso2 = eliminar_entonces(paso1)
        paso3 = aplicar_demorgan(paso2)
        paso4 = estandarizar_variables(paso3)
        paso5 = skolemizar(paso4)
        paso6 = quitar_universales(paso5)
        paso7 = distribuir_or(paso6)
        clausulas = separar_clausulas(paso7)
        resultado.extend(clausulas)
    return resultado
# Pruebas FNC
axiomas = [
    "Perro(Numa)",
    "AlaskanMalamute(Numa)",
    "∀x (AlaskanMalamute(x) → Peludo(x))",
    "∀x(AlaskanMalamute(x)→Perro(x))",
    "Gato(Brandi)",
    "∀x (Peludo(x) → (Perro(x) ∨ Gato(x)))"
]

cnf = forma_normal_conjuntiva(axiomas)

print("Cláusulas en Forma Normal Conjuntiva:")
for c in cnf:
    print(c)
    
#Punto 2. Unificacion
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

# Pruebas Unificacion
print(" ")
print("Unificación:")

# Ejemplo 1: variable v.s constante
c1 = ["Padre(x, Juan)"]
c2 = ["Padre(Pedro, Juan)"]
print("Ejemplo 1:")
print(unificacion(c1, c2))

# Ejemplo 2: dos variables v.s dos constantes
c1 = ["Amigo(x,y)"]
c2 = ["Amigo(Ana, Luis)"]
print("Ejemplo 2:")
print(unificacion(c1, c2))


# Punto 3. Refutacion

# Clase que define una cláusula donde se tiene la serie de literales que la conforman y con que cláusulas se ha resuelto
# durante el proceso de resolution
class Clausula:
    def __init__(self, clausulas):
        self.clausulas = clausulas
        self.resueltoCon = []
# Agregar una sentencia a la lista de axiomas.
def agregar_axioma(axiomas, sentencia):
    axiomas.append(sentencia)

# Verificar si hay cláusulas por resolver.
def hay_clausulas_por_resolver(clausulas):
    return any(len(c.clausulas) <= 1 and len(c.resueltoCon) < len(clausulas) - 1 for c in clausulas)


# Encontrar dos cláusulas por resolver.
def encontrar_clausulas_por_resolver(clausulas: [Clausula]):
    for i in range(0, len(clausulas)):
        for j in range(0, len(clausulas)):
            # Si las dos cláusulas no se han elegido para resolverse
            if (not clausulas[i].resueltoCon.__contains__(clausulas[j])) and (not i == j):
                clausulas[i].resueltoCon.append(clausulas[j])
                clausulas[j].resueltoCon.append(clausulas[i])
                for c1 in clausulas[i].clausulas:
                    for c2 in clausulas[j].clausulas:
                        # Si c1 tiene un literal que niega un literal de c2
                        if c1.split("(", 1)[0] == neg(c2.split("(", 1)[0]):
                            return clausulas[i], clausulas[j]
    return Clausula([]), Clausula([])

# Generar el resultado de la resolución.
def resolver(clausula1, clausula2):
    # Se busca los dos literales que se niegan para crear el resultado en el que se eliminan
    unificados = unificacion(clausula1.clausulas, clausula2.clausulas)
    resultado = []
    for u in unificados:
        resuelto = False
        n_u = []
        for c1 in u:
            esta = False
            for c2 in u:
                if c1 == neg(c2):
                    esta = True
                    resuelto = True
            if not esta:
                n_u.append(c1)
        if resuelto:
            resultado.append(Clausula([n for n in n_u]))
    return resultado


def distributiva(clausulas):
    for i, c in enumerate(clausulas):
        for c1 in c.clausulas:
            c2 = c1
            if c2[0] == "(":
                c2 = c2[1:-1]
            splt = c2.split("∧")
            if len(splt) > 1:
                for s in splt:
                    nueva = [cl for cl in c.clausulas if cl != c1]
                    nueva.append(s)
                    clausulas.append(Clausula(nueva))
                clausulas.pop(i)

# Agregar una nueva cláusula a la lista.
def agregar_clausula(clausulas, nueva_clausula):
    clausulas.append(nueva_clausula)


# Verificar si hay una cláusula nula en la lista.
def es_clausula_nula(clausulas: [Clausula]):
    # Hay cláusulas nulas si hay dos clausulas de un literal que se niegan entre si
    for c1 in clausulas:
        if len(c1.clausulas) == 1:
            for c2 in clausulas:
                if len(c2.clausulas) == 1:
                    if c1.clausulas[0] == neg(c2.clausulas[0]):
                        return True
    return False

def neg(literal: str) -> str:
    literal = literal.strip()
    if literal.startswith("¬"):
        return literal[1:]   # elimina la negación doble
    else:
        return "¬" + literal

from itertools import combinations

def refutacion(axiomas, sentencia, archivo_salida="clausulas.txt"):
    # Negar la sentencia y agregarla
    axiomas = list(axiomas)
    axiomas.append("¬" + sentencia)

    # A FNC
    fnc = forma_normal_conjuntiva(axiomas)

    # Normaliza
    fnc = [[_norm_lit(l) for l in c] for c in fnc]

    with open(archivo_salida, "w", encoding="utf-8") as f:
        # Guardar cláusulas iniciales
        f.write("Cláusulas en Forma Normal Conjuntiva:\n")
        print("\nCláusulas iniciales:")
        for c in fnc:
            print("  ", c)
            f.write("  " + str(c) + "\n")

        # Construir lista de cláusulas
        clausulas = [c[:] for c in fnc]

        paso = 1
        nuevos = True
        while nuevos:
            nuevos = False
            for i, j in combinations(range(len(clausulas)), 2):
                Ci, Cj = clausulas[i], clausulas[j]
                for li in Ci:
                    for lj in Cj:
                        theta = _unify_lits(li, lj)
                        if theta is None:
                            continue

                        resolvente = [ _apply_sigma(x, theta) for x in Ci if x != li ] + \
                                     [ _apply_sigma(x, theta) for x in Cj if x != lj ]

                        # quitar duplicados
                        res_clean = []
                        for r in resolvente:
                            if r not in res_clean:
                                res_clean.append(r)

                        # Mostrar y guardar el paso
                        paso_info = (
                            f"\nPaso {paso}: Resolver {Ci} y {Cj}\n"
                            f"  Literales complementarios: {li}  ⟂  {lj}\n"
                            f"  Sustitución: {theta}\n"
                            f"  Resolvente: {res_clean}\n"
                        )
                        print(paso_info)
                        f.write(paso_info)

                        if len(res_clean) == 0:
                            msg = "\n>>> Se encontró la cláusula nula. La sentencia está probada por refutación.\n"
                            print(msg)
                            f.write(msg)
                            return True
                        if res_clean not in clausulas:
                            clausulas.append(res_clean)
                            clausulas = sorted(clausulas, key=len)
                            nuevos = True
                            paso += 1

        msg = "\n>>> No fue posible llegar a contradicción. La sentencia no se puede probar.\n"
        print(msg)
        f.write(msg)
        return False

# Pruebas Refutacion

# Sentencia a probar
sentencia = "Peludo(Numa)"

# Ejecutar resolución por refutación
resultado = refutacion(axiomas, sentencia, "clausulas.txt")

print("\nResultado final:")
if resultado:
    print(f"La sentencia '{sentencia}' se puede probar por refutación")
else:
    print(f"La sentencia '{sentencia}' NO se puede probar")