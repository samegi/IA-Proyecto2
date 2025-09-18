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
        left, right = expr.split("→")
        return f"(¬{left.strip()} ∨ {right.strip()})"
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
    clausulas = []
    partes = expr.split("∧")
    for p in partes:
        p = p.replace("(", "").replace(")", "")
        literales = [lit.strip() for lit in p.split("∨")]
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
    "AlaskanMalamute(Numa)",                      
    "∀x (AlaskanMalamute(x) → Perro(x))",         
    "∀x (Perro(x) → Animal(x))",                  
    "∀x (AlaskanMalamute(x) → Peludo(x))"         
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

def refutacion(axiomas, sentencia, archivo_salida="clausulas.txt"):
    # Negar la sentencia y agregarla
    axiomas = list(axiomas)  # copia para no modificar original
    agregar_axioma(axiomas, neg(sentencia))

    # Convertir a forma normal conjuntiva
    fnc = forma_normal_conjuntiva(axiomas)

    # Guardar en archivo de texto
    with open(archivo_salida, "w") as f:
        f.write("Cláusulas en Forma Normal Conjuntiva:\n")
        for clausula in fnc:
            f.write(str(clausula) + "\n")

    # Construir las cláusulas iniciales (fnc ya devuelve listas de literales)
    clausulas = [Clausula(a) for a in fnc]
    distributiva(clausulas)

    print("\n--- INICIO RESOLUCIÓN POR REFUTACIÓN ---")
    paso = 1

    while hay_clausulas_por_resolver(clausulas):
        clausula1, clausula2 = encontrar_clausulas_por_resolver(clausulas)
        print(f"\nPaso {paso}: Resolver {clausula1.clausulas} y {clausula2.clausulas}")
        resultados = resolver(clausula1, clausula2)

        for resultado in resultados:
            print(f"  Resolvente obtenido: {resultado.clausulas}")
            if len(resultado.clausulas) > 0 and not any(c.clausulas == resultado.clausulas for c in clausulas):
                agregar_clausula(clausulas, resultado)
                clausulas = sorted(clausulas, key=lambda c: len(c.clausulas))
                print(f"  -> Nueva cláusula agregada: {resultado.clausulas}")

        if es_clausula_nula(clausulas):
            print("\n>>> Se encontró la cláusula nula. La sentencia está probada por refutación.")
            return True

        paso += 1

    print("\n>>> No fue posible llegar a contradicción. La sentencia no se puede probar.")
    return False


# Sentencia a probar
sentencia = "Peludo(Numa)"

# Ejecutar resolución por refutación
resultado = refutacion(axiomas, sentencia, "clausulas.txt")

print("\nResultado final:")
if resultado:
    print(f"La sentencia '{sentencia}' se puede probar por refutación")
else:
    print(f"La sentencia '{sentencia}' NO se puede probar")