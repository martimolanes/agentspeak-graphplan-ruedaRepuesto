/// Código en AgentSpeak implementando Graphplan ejemplificando con el Problema de la Rueda de Repuesto.

// Creencias Iniciales
en(pinchada,eje).
en(repuesto,maletero).

// acciones(Accion, Efectos, Precondiciones)
accion(quitar(repuesto,maletero),
    [not_en(repuesto,maletero), en(repuesto,suelo)],
    [en(repuesto, maletero)]
).
accion(quitar(pinchada,eje),
    [not_en(pinchada,eje), en(pinchada,suelo)],
    [en(pinchada, eje)]
).
accion(colocar(repuesto,eje),
    [en(repuesto,eje), not_en(repuesto,suelo)],
    [not_en(pinchada,eje), en(repuesto,suelo)]
).
accion(dejarloSinVigilarDeNoche,
    [not_en(repuesto,maletero), not_en(pinchada,eje), not_en(repuesto,eje), not_en(pinchada,suelo), not_en(repuesto,suelo)],
    []
).

// Goals
!start([en(repuesto,eje)]).
//!start([not_en(pinchada,eje),en(repuesto,suelo)]).

// Planes
+!start(Objetivo) <-
    .findall(en(R,S), en(R,S), IB);
    .sort(IB, InitialBeliefs);
    .printf("Creencias iniciales: %s\n", InitialBeliefs);

    .print("Acciones, Efectos y Precondiciones: ");
    .findall([Acciones, Efectos, Precondiciones], accion(Acciones, Efectos, Precondiciones), Lista);
    for ( .member(X, Lista) ) {
        .print(X);
    };
    .print("-------------------------------------------------------------");
    .printf("Buscando camino hacia Objetivo: %s\n\n", Objetivo);

    !find(Objetivo).

+!find(Objetivo) <-
    .queue.create(Acciones);
    for ( .member(ObjetivoActual, Objetivo) ) { // Por cada Objetivo
        // Encontrar Acciones que tengan como efecto el Objetivo
        .findall(Acc, (accion(Acc, Efectos, _) & .member(ObjetivoActual, Efectos)), AccionesQueCumplenObjetivo);
        .queue.add(Acciones, AccionesQueCumplenObjetivo);
    }
    .print("-------------------------------------------------------------");
    .printf("Lista de Acciones que cumplen cada objetivo: %s\n", Acciones);

    .queue.to_list(Acciones, AccionesList);
    .nth(0, AccionesList, PrimeraAccion);

    .queue.create(Combinaciones);
    for (.member(Combinar, PrimeraAccion)) {
        .queue.add(Combinaciones, [Combinar]);
    };

    .length(Acciones, AccionesLength);

    for (.range(Idx, 1, AccionesLength - 1)) {
        .queue.create(CombinationsAux);
        .nth(Idx, AccionesList, CurrentAccion);
        for (.member(ParaCombinar, CurrentAccion)) {
            // .print("ParaCombinar: ", ParaCombinar);
            for (.member(Comb, Combinaciones)) {
                // .print("Comb: ", Comb);
                .queue.add(CombinationsAux, [ParaCombinar | Comb]);
            };
        };
        .queue.to_list(CombinationsAux, CombinationsAuxList);
        .queue.clear(Combinaciones);
        for (.member(Cmb, CombinationsAuxList)) {
            .reverse(Cmb, CmbRev); // para conservar el orden en el print
            .queue.add(Combinaciones, CmbRev);
        };
    };

    .print("Combinaciones: ", Combinaciones);

    // Filtrar todas las combinaciones válidas
    .findall(Comb, (.member(Comb, Combinaciones) & no_conflict_in_combination(Comb)), CombinacionesValidas);
    .printf("Combinaciones válidas: %s\n", CombinacionesValidas);

    if( .length(CombinacionesValidas) > 0 ) {
        // e.g. [[quitar(repuesto,maletero), ...], [quitar(pinchada,eje), ...], ...];
        .queue.create(Preconds);
        for ( .member(CombinacionValida, CombinacionesValidas) ) { 
            //.print("CombinacionValida: ", CombinacionValida);
            //e.g. [quitar(repuesto,maletero), ...]
            for ( .member(Accion, CombinacionValida) ) {
                .findall(Precnd, accion(Accion, _, Precnd), PrecondsPorAccion);
                //.print("Precondiciones de la acción: ", PrecondsPorAccion);
                // e.g. [[en(repuesto,maletero),...], ...]]
                for( .member(Precond, PrecondsPorAccion) ) {
                    // e.g. [en(repuesto,maletero),...]
                    for (.member(P, Precond)) {
                        .queue.add(Preconds, P);
                    };
                };
            }
        };

        .print("Comparamos las precondiciones con las creencias iniciales");
        .print("Precondiciones de las acciones: ", Preconds);

        .findall(en(R,S), en(R,S), IB);
        .sort(IB, InitialBeliefs);
        .printf("Creencias iniciales: %s", InitialBeliefs);

        .queue.to_list(Preconds,PrecondList);
        // Compara si la Lista de Precondiciones coincide con las Creencias Iniciales
        // si no, sigue con la búsqueda de las Precondiciones
        if( .intersection(PrecondList, InitialBeliefs, InitialBeliefs) ) {
            .print("\n\n  ========== Éxito: Camino encontrado ========== ");
        } else {
            .print("Salto Recursivo con las Precondiciones como Objetivo\n\n");
            !find(Preconds);
        }
    } else {
        .print("\nNO EXISTE UNA SOLUCIÓN POSIBLE");
    }.

// Conflicto debido a Efectos Inconsistentes
// (e.g., una acción tiene un efecto y otra tiene su negación)
conflict_effects(A1, A2) :-
    accion(A1, E1, _) &
    accion(A2, E2, _) &
    (
        (.member(en(X,Y), E1) & .member(not_en(X,Y), E2)) |
        (.member(not_en(X,Y), E1) & .member(en(X,Y), E2))
    ).

// Conflicto debido a necesidades en competencia 
// (e.g., una acción requiere una precondición y otra requiere su negación)
conflict_preconditions(A1, A2) :-
    accion(A1, _, P1) &
    accion(A2, _, P2) &
    (
        (.member(en(X,Y), P1) & .member(not_en(X,Y), P2)) |
        (.member(not_en(X,Y), P1) & .member(en(X,Y), P2))
    ).

// Interferencia
// (e.g., el efecto de una acción niega la precondición de otra)
interference(A1, A2) :-
    accion(A1, E1, _) &
    accion(A2, _, P2) &
    (
        (.member(en(X,Y), E1) & .member(not_en(X,Y), P2)) |
        (.member(not_en(X,Y), E1) & .member(en(X,Y), P2))
    ).

// Regla de Conflicto General: true si existe algún conflicto entre dos acciones
conflict(A1, A2) :-
    conflict_effects(A1, A2) |
    conflict_preconditions(A1, A2) |
    interference(A1, A2) |              // si A1 interfiere con A2
    interference(A2, A1).               // del otro lado

// True si no existe ninguna pareja de acciones con conflictos entre las combinaciones
// es decir, si no existe ninguna exclusión mutuamente excluyente
no_conflict_in_combination(Comb) :-
    not (exists_pair(Comb, A1, A2) & conflict(A1, A2)).

// Identifica parejas de acciones únicas en una combinación
exists_pair(Comb, A1, A2) :-
    .nth(I, Comb, A1) &
    .nth(J, Comb, A2) &
    I < J.
