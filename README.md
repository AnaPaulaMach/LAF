# LAF - Implementacion del formalismo

Este README documenta la implementacion del formalismo **Label-Based Argumentation Framework (LAF)** en este monorepo.

No reemplaza los README de `API/` y `UI/`: esos documentos cubren ejecucion local, scripts y entorno. Este archivo se enfoca en la **semantica del modelo** y en como se implementa en backend y frontend.

## 1) Modelo conceptual implementado

El sistema trabaja sobre programas formados por:

- **Hechos**: `predicado(termino). {label_1; label_2; ...}`
- **Reglas**: `cabeza(X) :- cuerpo1(X), cuerpo2(X), ... {label_1; label_2; ...}`

Cada hecho o regla porta un vector de labels. Cada posicion del vector representa un atributo independiente dentro de la algebra de etiquetas.

## 2) Sintaxis de labels

La sintaxis actual separa labels con **punto y coma**:

- Correcto: `{0.75; 0.95}`
- Correcto: `{0.5; [0.6, 1.0]}`
- Incorrecto: `{0.75, 0.95}` (la coma no separa labels)

La coma se reserva para extremos de intervalos numericos dentro de corchetes.

## 3) Labels numericos y cualitativos

### 3.1 Numericos

- Se interpretan como valores en `[0, 1]`.
- Las operaciones de soporte, agregacion y conflicto se aplican por atributo.

### 3.2 Cualitativos

- Se interpretan como conjuntos de simbolos (tokens separados por espacios).
- Operadores disponibles: `Union`, `Intersection` y `Difference`.
- Los tres operadores pueden usarse en cualquiera de las tres operaciones (soporte, agregacion, conflicto); no hay restriccion de cual keyword va en cual campo.
- `Difference` es asimetrico (`X \ Y`): en soporte y agregacion, `X` es el acumulador y `Y` el siguiente valor incorporado; en conflicto, `X` es el hecho atacado y `Y` el hecho atacante.

## 4) Intervalos en labels numericos

Un atributo numerico puede declararse como intervalo:

- Ejemplo: `basicServices(houseA). {0.5; [0.6, 1.0]}`

Semantica implementada:

1. El intervalo se normaliza como `[min, max]` (si viene invertido, se corrige).
2. Para la inferencia inicial se usa el **extremo menor** (`min`).
3. Se conserva metadata del intervalo para la interaccion en UI.

Esto aplica tanto a hechos como a reglas.

## 5) Flujo de inferencia LAF en el backend

El motor sigue este orden conceptual:

1. Carga hechos iniciales.
2. Activa reglas cuando el cuerpo queda satisfecho.
3. Calcula **soporte** para hechos derivados.
4. Ejecuta **agregacion** cuando hay derivaciones equivalentes.
5. Detecta contradicciones `p(X)` vs `~p(X)` y aplica **conflicto**.
6. Devuelve el grafo argumentativo con nodos y aristas tipadas.

## 6) Representacion del grafo y visualizacion

La salida conserva la estructura argumentativa para visualizacion:

- Nodos de hechos y reglas
- Relaciones de soporte/agregacion/conflicto
- Valores `mu` y `delta` por atributo

Para nodos originados en el programa, la respuesta incluye metadata de intervalos y claves de origen estables para habilitar control interactivo en la UI.

## 6.1) Narrativa del experimento desde el grafo

El sistema incluye un flujo de proceso completo (`/api/graph/process`) que, ademas de construir el grafo, genera una narrativa en ingles basada en:

- conclusiones finales,
- como se obtuvieron,
- conflictos detectados,
- y resultado (ganador) de cada conflicto.

La narrativa se construye a partir de una traza estructurada derivada del grafo y luego se redacta con un LLM configurable por API key.

Semantica cuantitativa usada en la traza:

- **DEFEATED**: todos los `delta` numericos de la conclusion son `0.0`.
- **ADMISSIBLE**: al menos un `delta` numerico de la conclusion es `> 0.0`.

## 7) Interaccion de intervalos en la UI

La interfaz permite ajustar labels intervalares desde el detalle del nodo:

- El detalle aparece en una **ventana flotante** sobre el grafo.
- Las barras de `mu` mantienen referencia global `0..1`.
- El control deslizante solo se mueve dentro del tramo editable del intervalo.
- Al confirmar el cambio, se reprocesa el programa y se redibuja el grafo con los nuevos valores seleccionados.

## 8) Alcance de este documento

Este README define el marco de implementacion del formalismo LAF en el monorepo.

Para ejecutar backend/frontend, scripts y entorno, ver:

- `API/README.md`
- `UI/README.md`

## 9) Diferencias de este fork (AnaPaulaMach/LAF) respecto del repositorio original

Este fork se usa en el trabajo final de Ana Paula Machado (recomendador argumentativo sobre reseñas de café). Respecto de
`JaviDebortoli/LAF` añade dos cambios, ambos en `main`:

1. **Propagación con valoraciones debilitadas** (`API/src/main/java/Argumentation/LAF/Domain/InferenceEngine.java`,
   `relabelWithWeakenedPremises`). El motor original continuaba cada cadena de reglas con el apoyo acumulado μ de las
   premisas y resolvía los conflictos una sola vez al final. Budán et al. (2017), Definición 8(iii) y Algoritmo 2, continúan
   con el apoyo debilitado δ. El fork añade, después de construir el grafo y detectar los conflictos, un reetiquetado que
   resuelve las ecuaciones de la Definición 8 por iteración. Se activa por defecto; `LAF_PROPAGATION=accrued`
   (o `-Dlaf.propagation=accrued`) restaura el comportamiento original. Pruebas en `InferenceEngineWeakenedPropagationTest`.
2. **UI desplegable fuera de Docker Compose**: `UI/nginx.conf.template` toma el backend de la variable `API_UPSTREAM`
   (por defecto `api:8080`).

**Alcance y límites de la corrección 1, para quien quiera reutilizarla:**

- Es general para el etiquetado numérico: vale para cualquier programa, álgebra numérica y número de etiquetas. Las etiquetas
  cualitativas (Union/Intersection/Difference) no se reetiquetan y conservan el comportamiento original.
- Es **exacta en grafos sin ciclos de conflicto** (por ejemplo, cadenas evidencia → aspecto → dimensión → recomendación, el
  caso de este trabajo). Con ciclos de conflicto (Fig. 5b–c del artículo) la iteración converge a un punto fijo del sistema,
  que es una de sus soluciones; el artículo delega ese caso a un solver externo que aquí no se implementa.
- **No corrige la construcción del grafo.** Se detectó un defecto independiente del motor original: cuando un literal aparece
  como hecho del programa y además se deriva por una regla, el motor pierde la agregación y no vuelve a disparar las reglas que
  dependen de él (sonda mínima: `a(x). {0.5}`, `b(x). {0.5}`, `a(X) :- b(X). {1}`, `d(X) :- a(X). {1}` → `d` no se deriva).
  El reetiquetado trabaja sobre el grafo ya construido, así que hereda ese defecto. No afecta a programas cuyos hechos son solo
  hojas (el caso de este trabajo); sí afecta, por ejemplo, al Ejemplo 1 del artículo (`buy(houseB)`).
- Verificación disponible: control sintético (0,3913 → 0,45), 198 pares producto–aspecto contra un cálculo manual de la
  Definición 8, y el Ejemplo 1 del artículo (casa B reproduce la Fig. 7 salvo por el defecto anterior).

**Ejecutar localmente:** `docker compose up --build` en la raíz (API en `http://localhost:8080`, UI en `http://localhost:80`),
o `cd API && mvnw.cmd spring-boot:run` y `cd UI && npm ci && npm start`. Para el comportamiento original: `LAF_PROPAGATION=accrued`.
