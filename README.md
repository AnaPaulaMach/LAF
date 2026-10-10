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

## 9) Cambios de este fork

Dos cambios respecto del repositorio del que se deriva, ambos en `main`:

1. **Propagación con valoraciones debilitadas** (`InferenceEngine.relabelWithWeakenedPremises`). Tras construir el grafo y
   detectar los conflictos, el motor recalcula las etiquetas de modo que el soporte de cada conclusión use el valor
   debilitado (δ) de sus premisas, no el acumulado (μ). `LAF_PROPAGATION=accrued` restaura el comportamiento anterior.
   Pruebas en `InferenceEngineWeakenedPropagationTest`.
2. **UI desplegable fuera de Docker Compose**: `UI/nginx.conf.template` toma el backend de `API_UPSTREAM` (por defecto `api:8080`).

Alcance del cambio 1:

- Vale para cualquier programa con etiquetas numéricas. Las etiquetas cualitativas no se reetiquetan.
- Es exacto en grafos sin ciclos de conflicto (cadenas del tipo evidencia → aspecto → dimensión → recomendación). Con ciclos
  de conflicto, la iteración aproxima un punto fijo.
- No modifica la construcción del grafo. Un defecto previo se mantiene: si un literal es hecho del programa y además se
  deriva por una regla, se pierde su agregación y no se disparan las reglas que dependen de él. No afecta a programas cuyos
  hechos son solo hojas.

Ejecución local: `docker compose up --build` en la raíz (API en `http://localhost:8080`, UI en `http://localhost:80`), o
`cd API && mvnw.cmd spring-boot:run`.
