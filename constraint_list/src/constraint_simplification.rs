// Uncomment lines 163, 165, 336 and 338 to print cluster information
use super::{ConstraintStorage, A, C, S, HashConstraint};
use crate::SignalMap;
use crate::clusters_utils::{Cluster, ClusterArena, ClusterPath};

use circom_algebra::num_bigint::BigInt;
use std::collections::{HashMap, HashSet, LinkedList, BTreeMap};
use std::fs;
use std::sync::Arc;





fn build_clusters(linear: LinkedList<C>, no_vars: usize) -> Vec<Cluster<C>> {

    let no_linear = LinkedList::len(&linear);
    let mut arena = ClusterArena::with_capacity(no_linear);
    let mut cluster_to_current = ClusterPath::with_capacity(no_linear);
    let mut signal_to_cluster = vec![no_linear; no_vars];
    for constraint in linear {
        let signals = C::take_cloned_signals(&constraint);
        let dest = ClusterArena::len(&arena);
        ClusterArena::push(&mut arena, Some(Cluster::new(constraint)));
        Vec::push(&mut cluster_to_current, dest);
        for signal in signals {
            let prev = signal_to_cluster[signal];
            signal_to_cluster[signal] = dest;
            if prev < no_linear {
                crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, prev, dest);
            }
        }
    }
    let mut clusters = Vec::new();
    for cluster in arena {
        if let Some(cluster) = cluster {
            if Cluster::size(&cluster) != 0 {
                Vec::push(&mut clusters, cluster);
            }
        }
    }
    clusters
}

fn build_clusters_nonlinear(
    storage: &ConstraintStorage,
) -> LinkedList<ConstraintStorage> {

    let no_constraints = storage.get_no_constraints();
    let mut arena = ClusterArena::with_capacity(no_constraints);
    let mut cluster_to_current = ClusterPath::with_capacity(no_constraints);
    let mut monomial_to_cluster = HashMap::new();

    for c_id in storage.get_ids() {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !constraint.is_empty(){
            let monomials = C::take_possible_cloned_monomials(&constraint);
            let dest = ClusterArena::len(&arena);
            ClusterArena::push(&mut arena, Some(Cluster::new(c_id)));
            Vec::push(&mut cluster_to_current, dest);
            for (monomial, _) in monomials {
                match monomial_to_cluster.get(&monomial){
                    Some(cluster) =>{
                        let prev = cluster;
                        crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, *prev, dest);
                        monomial_to_cluster.insert(monomial, dest);       
                    }, 
                    None => {
                        monomial_to_cluster.insert(monomial, dest);
                    },
                }
            }
        }
    }

    let mut clusters = LinkedList::new();
    for cluster in arena {
        if let Some(cluster) = cluster {

            if cluster.size() > 1{
                let mut new_storage = ConstraintStorage::new();
    
                for constraint_id in cluster.constraints{
                    let constraint = storage.read_constraint(constraint_id).unwrap();
                    let prev_constraint_id = storage.read_constraint_prev_id(constraint_id).unwrap();
                    new_storage.add_constraint_with_prev_id(constraint, prev_constraint_id);
                }
                clusters.push_back(new_storage);
            }
        }
    }
    clusters
}

fn get_clusters_quadratic_equalities(
    storage: &ConstraintStorage,
    no_vars: usize,
) -> Vec<Cluster<C>> {

    let no_constraints = storage.get_no_constraints();
    let mut arena = ClusterArena::with_capacity(no_constraints);
    let mut cluster_to_current = ClusterPath::with_capacity(no_constraints);
    let mut signal_to_cluster = vec![no_constraints; no_vars];

    for c_id in storage.get_ids() {
        let constraint = storage.read_constraint(c_id).unwrap();
        if C::is_quadratic_equality(&constraint){
            let signals = C::take_cloned_signals(&constraint);
            let dest = ClusterArena::len(&arena);
            ClusterArena::push(&mut arena, Some(Cluster::new(constraint)));
            Vec::push(&mut cluster_to_current, dest);
            for signal in signals {
                let prev = signal_to_cluster[signal];
                signal_to_cluster[signal] = dest;
                if prev < no_constraints {
                    crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, prev, dest);
                }
            }
        }
    }

    let mut clusters = Vec::new();
    for cluster in arena {
        if let Some(cluster) = cluster {
            if Cluster::size(&cluster) != 0 {
                Vec::push(&mut clusters, cluster);
            }
        }
    }
    clusters
}


fn get_clusters_definitions(
    storage: &ConstraintStorage,
    no_vars: usize,
) -> (Vec<Cluster<C>>, Vec<Vec<usize>>) {

    let no_constraints = storage.get_no_constraints();
    let mut arena = ClusterArena::with_capacity(no_constraints);
    let mut cluster_to_current = ClusterPath::with_capacity(no_constraints);
    let mut signal_to_clusters: Vec<LinkedList<usize>> = vec![LinkedList::new(); no_vars];
    let mut signal_to_its_cluster = HashMap::new();
    let mut cluster_to_signals: Vec<HashSet<usize>> = Vec::new();

    for c_id in storage.get_ids() {
        let constraint = storage.read_constraint(c_id).unwrap();
        if C::is_quadratic_equality(&constraint){
            let (signal_a, signal_b, signal_c) = C::take_signals_quadratic_equality(&constraint);
            let dest = ClusterArena::len(&arena);
            ClusterArena::push(&mut arena, Some(Cluster::new(constraint)));
            Vec::push(&mut cluster_to_current, dest);
            let mut new_signals: HashSet<usize> = HashSet::new();
            for prev in &signal_to_clusters[signal_c]{
                //println!("Uniendo clusters {} {}", *prev, dest);
                crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, *prev, dest);
                let mut new_signals = HashSet::new();
                for s in &cluster_to_signals[*prev]{
                    new_signals.insert(*s);
                }
            }
            match signal_to_its_cluster.get(&signal_a){
                Some(prev) =>{
                    //println!("Uniendo clusters {} {}", *prev, dest);
                    crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, *prev, dest);
                    for s in &cluster_to_signals[*prev]{
                        new_signals.insert(*s);
                    }
                },
                None => {},
            }
            match signal_to_its_cluster.get(&signal_b){
                Some(prev) =>{
                    //println!("Uniendo clusters {} {}", *prev, dest);
                    crate::clusters_utils::arena_merge(&mut arena, &mut cluster_to_current, *prev, dest);
                    for s in &cluster_to_signals[*prev]{
                        new_signals.insert(*s);
                    }
                },
                None => {},
            }
            
            cluster_to_signals.push(new_signals);

            signal_to_its_cluster.insert(signal_c, dest);
            signal_to_clusters[signal_a].push_back(dest);
            signal_to_clusters[signal_b].push_back(dest);
            signal_to_clusters[signal_c].push_back(dest);
            cluster_to_signals[dest].insert(signal_a);
            cluster_to_signals[dest].insert(signal_b);
            cluster_to_signals[dest].insert(signal_c);
        }
    }


    let mut clusters = Vec::new();
    let mut final_signal_to_clusters = vec![Vec::new(); no_vars];
    for i in 0..arena.len() {
        if let Some(cluster) = &arena[i] {
            if Cluster::size(&cluster) > 1 {
                let pos = clusters.len();
                Vec::push(&mut clusters, cluster.clone());
                for s in &cluster_to_signals[i]{
                    final_signal_to_clusters[*s].push(pos);
                }

            }
        }
    }
    (clusters, final_signal_to_clusters)
}

fn generate_possible_combinations_clusters(signal_to_clusters: &Vec<Vec<usize>>) 
-> (HashSet<(usize, usize)>, HashSet<(usize, usize)>){
    let mut once_shared = HashSet::new();
    let mut multiple_shared = HashSet::new();
    
    for clusters in signal_to_clusters{

        for pos_i in 0..clusters.len(){
            for pos_j in pos_i + 1..clusters.len(){
                let new_combination = (clusters[pos_i], clusters[pos_j]);
                if once_shared.contains(&new_combination){
                    multiple_shared.insert(new_combination);
                }
                else{
                    once_shared.insert(new_combination);
                }
            }
        }

    }
    (once_shared, multiple_shared)
}


fn rebuild_witness(max_signal: usize, deleted: HashSet<usize>) -> SignalMap {
    let mut map = SignalMap::with_capacity(max_signal);
    let mut free = LinkedList::new();
    for signal in 0..max_signal {
        if deleted.contains(&signal) {
            free.push_back(signal);
        } else if let Some(new_pos) = free.pop_front() {
            map.insert(signal, new_pos);
            free.push_back(signal);
        } else {
            map.insert(signal, signal);
        }
    }
    map
}



fn linear_simplification(
    linear: LinkedList<C>,
    forbidden: Arc<HashSet<usize>>,
    no_labels: usize,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>) {
    use circom_algebra::simplification_utils::full_simplification;
    use circom_algebra::simplification_utils::Config;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    ////println!("Cluster simplification");
    let mut cons = LinkedList::new();
    let mut substitutions = LinkedList::new();
    let clusters = build_clusters(linear, no_labels);
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let no_clusters = Vec::len(&clusters);
    // //println!("Clusters: {}", no_clusters);
    let mut id = 0;
    for cluster in clusters {
        let n = Cluster::size(&cluster);
        let cluster_tx = cluster_tx.clone();
        let config = Config {
            field: field.clone(),
            constraints: cluster.constraints,
            forbidden: Arc::clone(&forbidden),
        };
        let job = move || {
            //println!("cluster: {}, {}", id,n);
            let result = full_simplification(config);
             //println!("End of cluster: {}", id);
            cluster_tx.send(result).unwrap();
        };
        ThreadPool::execute(&pool, job);
        let _ = id;
        id += 1;
    }
    ThreadPool::join(&pool);
    //println!("Sale del tratamiento de clusters");
    for _ in 0..no_clusters {
        let mut result = simplified_rx.recv().unwrap();
        LinkedList::append(&mut cons, &mut result.constraints);
        LinkedList::append(&mut substitutions, &mut result.substitutions);
    }
    (substitutions, cons)
}


fn non_linear_simplification(
    deduced_constraints_hash: &mut HashSet<HashConstraint>,
    clusters: LinkedList<ConstraintStorage>,
    forbidden: Arc<HashSet<usize>>,
    field: &BigInt,
) -> (LinkedList<S>, LinkedList<C>, LinkedList<usize>, usize) {
    use circom_algebra::simplification_utils::full_simplification;
    use circom_algebra::simplification_utils::Config;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    //println!("Cluster simplification");
    ////println!("Numero total de constraints: {}", storage.get_no_constraints());
    let mut cons = LinkedList::new();
    let mut delete = LinkedList::new();
    let mut minimal_clusters = LinkedList::new();
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    let mut no_clusters = 0;
    // //println!("Clusters: {}", no_clusters);
    let mut id = 0;

    for cluster in clusters {
            no_clusters = no_clusters + 1;
            let cluster_tx = cluster_tx.clone();

            let config = crate::non_linear_simplification::NonLinearClustersConfig {
                storage: cluster,
                field: field.clone(),
            };
            let job = move || {
                let new_clusters = crate::non_linear_simplification::obtain_non_linear_clusters(config);
                cluster_tx.send(new_clusters).unwrap();
            };
            ThreadPool::execute(&pool, job);

            let _ = id;
            id += 1;
        
    }
    ThreadPool::join(&pool);
    for _ in 0..no_clusters {
        let mut new_clusters = simplified_rx.recv().unwrap();

        LinkedList::append(&mut minimal_clusters, &mut new_clusters);
    }
    //println!("Calculados clusters minimos. Un total de {} clusters", minimal_clusters.len());
    let mut j = 0;
    for i in &minimal_clusters{
        //println!("Cluster {} con tamanyo {}",j,i.no_constants());
        j = j +1;
    }
    let (cluster_tx, simplified_rx) = mpsc::channel();
    let pool = ThreadPool::new(num_cpus::get());
    no_clusters = 0;
    for cluster in minimal_clusters {
        no_clusters = no_clusters + 1;
        let cluster_tx = cluster_tx.clone();

        let config = crate::non_linear_simplification::NonLinearConfig {
            field: field.clone(),
            storage: cluster,
            forbidden: Arc::clone(&forbidden),
        };

        let job = move || {
            let (new_constraints, to_delete) = crate::non_linear_simplification::deduce_linear_constraints(config);
            cluster_tx.send((new_constraints, to_delete)).unwrap();
        };
        ThreadPool::execute(&pool, job);

        let _ = id;
        id += 1;
    
    }
    ThreadPool::join(&pool);
    ////println!("Calculadas nuevas lineales");
    for _ in 0..no_clusters {
        let (mut new_constraints, mut new_delete) = simplified_rx.recv().unwrap();   
        LinkedList::append(&mut cons, &mut new_constraints);
        LinkedList::append(&mut delete, &mut new_delete);
    }

    for c in &cons{
        if deduced_constraints_hash.contains(&C::get_hash_constraint(&c, field)){
            //println!("Repetida:");
            //println!("Linear Expression C: ");
             for c2 in c.c(){
                 //println!("     Signal: {:}",c2.0);
                 //println!("     Value : {:}",c2.1.to_string());
             }
        }

        deduced_constraints_hash.insert(C::get_hash_constraint(&c, field));
    }

    let num_new_linear = cons.len();
    let config = Config {
        field: field.clone(),
        constraints: cons,
        forbidden: Arc::clone(&forbidden),
    };


    let result = full_simplification(config);
    (result.substitutions, result.constraints, delete, num_new_linear)
}

type SignalToConstraints = HashMap<usize, LinkedList<usize>>;
fn build_non_linear_signal_map(non_linear: &ConstraintStorage) -> SignalToConstraints {
    let mut map = SignalToConstraints::new();
    for c_id in non_linear.get_ids() {
        let constraint = non_linear.read_constraint(c_id).unwrap();
        for signal in C::take_cloned_signals(&constraint) {
            if let Some(list) = map.get_mut(&signal) {
                list.push_back(c_id);
            } else {
                let mut new = LinkedList::new();
                new.push_back(c_id);
                map.insert(signal, new);
            }
        }
    }

    map
}


// type SetConstraints = HashSet<(Vec<(usize, BigInt)>, Vec<(usize, BigInt)>, Vec<(usize, BigInt)>)>;

// fn build_non_linear_hashset(non_linear: &mut ConstraintStorage, field: &BigInt) -> SetConstraints {
//     let mut set = SetConstraints::new();
//     for c_id in non_linear.get_ids() {
//         let mut constraint = non_linear.read_constraint(c_id).unwrap();
//         if !C::is_empty(&constraint){
//         //     let hash = C::get_hash_constraint(&constraint, field);
//         //     if set.contains(&hash){
//         //         non_linear.replace(c_id, C::empty());
//         //     }   
//         //     else{
//                 circom_algebra::algebra::Constraint::fix_normalize_constraint(&mut constraint, field);
//                 non_linear.replace(c_id, constraint);
//         //         set.insert(hash);
//         //     }
//         }
//     }
//     set
// }


fn normalize_constraints(non_linear: &mut ConstraintStorage, field: &BigInt) {
    for c_id in non_linear.get_ids() {
        let mut constraint = non_linear.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){

                circom_algebra::algebra::Constraint::fix_normalize_constraint(&mut constraint, field);
                non_linear.replace(c_id, constraint);
        }
    }
}


fn apply_substitution_to_map(
    storage: &mut ConstraintStorage,
    map: &mut SignalToConstraints,
    substitutions: &LinkedList<S>,
    field: &BigInt,
) -> LinkedList<C> {
    fn constraint_processing(
        storage: &mut ConstraintStorage,
        map: &mut SignalToConstraints,
        c_ids: &LinkedList<usize>,
        substitution: &S,
        field: &BigInt,
    ) -> LinkedList<usize> {
        let mut linear = LinkedList::new();
        let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
        for c_id in c_ids {
            let c_id = *c_id;
            let mut constraint = storage.read_constraint(c_id).unwrap();
            C::apply_substitution(&mut constraint, substitution, field);
            if C::is_linear(&constraint) {
                linear.push_back(c_id);
            }
            storage.replace(c_id, constraint);
            for signal in &signals {
                if let Some(list) = map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    map.insert(*signal, new);
                }
            }
        }
        linear
    }

    let mut linear_id = LinkedList::new();
    for substitution in substitutions {
        if let Some(c_ids) = map.get(substitution.from()).cloned() {
            let mut new_linear = constraint_processing(storage, map, &c_ids, substitution, field);
            linear_id.append(&mut new_linear);
        }
    }
    let mut linear = LinkedList::new();
    for c_id in linear_id {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){
            linear.push_back(constraint);
            storage.replace(c_id, C::empty());
        }
    }
    linear
}


fn apply_substitution_to_map_non_linear(
    storage: &mut ConstraintStorage,
    map: &mut SignalToConstraints,
    substitutions: &LinkedList<S>,
    field: &BigInt,
) -> LinkedList<C> {
    fn constraint_processing(
        storage: &mut ConstraintStorage,
        map: &mut SignalToConstraints,
        c_ids: &LinkedList<usize>,
        substitution: &S,
        field: &BigInt,
    ) -> LinkedList<usize> {
        let mut linear = LinkedList::new();
        let signals: LinkedList<_> = substitution.to().keys().cloned().collect();
        for c_id in c_ids {
            let c_id = *c_id;
            let mut constraint = storage.read_constraint(c_id).unwrap();
            C::apply_substitution_normalize(&mut constraint, substitution, field);
            if C::is_linear(&constraint) {
                linear.push_back(c_id);
            }
            storage.replace(c_id, constraint);
            for signal in &signals {
                if let Some(list) = map.get_mut(&signal) {
                    list.push_back(c_id);
                } else {
                    let mut new = LinkedList::new();
                    new.push_back(c_id);
                    map.insert(*signal, new);
                }
            }
        }
        linear
    }

    let mut linear_id = LinkedList::new();
    for substitution in substitutions {
        if let Some(c_ids) = map.get(substitution.from()).cloned() {
            let mut new_linear = constraint_processing(storage, map, &c_ids, substitution, field);
            linear_id.append(&mut new_linear);
        }
    }
    let mut linear = LinkedList::new();
    for c_id in linear_id {
        let constraint = storage.read_constraint(c_id).unwrap();
        if !C::is_empty(&constraint){
            linear.push_back(constraint);
            storage.replace(c_id, C::empty());
        }
    }
    linear
}



fn remove_redundant_constraints(constraint_storage: &mut ConstraintStorage, field: &BigInt){
    let mut set_constraints = HashSet::new();
    for cid in constraint_storage.get_ids(){
        let constraint = constraint_storage.read_constraint(cid).unwrap();
        let hash_constraint = C::get_hash_constraint(&constraint, field);
        if set_constraints.contains(&hash_constraint){
            constraint_storage.replace(cid, C::empty());
        }
        else{
            set_constraints.insert(hash_constraint);
        }
    }
}

pub fn simplification(mut linear: LinkedList<C>, constraint_storage: &mut ConstraintStorage, mut forb: HashSet<usize>, no_labels: usize, max_signal: usize,  field: BigInt, apply_simp: bool,
    witness: BTreeMap<usize, BigInt>) -> (SignalMap,BTreeMap<usize,BigInt>) {
    use circom_algebra::simplification_utils::build_encoded_fast_substitutions;
    use circom_algebra::simplification_utils::fast_encoded_constraint_substitution;
    use std::time::SystemTime;
    use std::sync::mpsc;
    use threadpool::ThreadPool;

    let mut round_id = 0;
    let _ = round_id;
    let mut apply_round = !linear.is_empty();
    let forbidden = Arc::new(std::mem::replace(&mut forb, HashSet::with_capacity(0)));
    let mut deleted = HashSet::new();
    let mut non_linear_map = if true {
        // //println!("Building non-linear map");
        let now = SystemTime::now();
        let non_linear_map = build_non_linear_signal_map(&constraint_storage);
        let _dur = now.elapsed().unwrap().as_millis();
        // //println!("Non-linear was built in {} ms", dur);
        non_linear_map
    } else {
        SignalToConstraints::with_capacity(0)
    };


    //println!("Comienza la simplificacion lineal.");
    while apply_round {
        let now = SystemTime::now();
        // //println!("Number of linear constraints: {}", linear.len());
        //println!("El numero de lineales que le envio es: {}", linear.len());
        let (substitutions, mut constants) = linear_simplification(
            linear,
            Arc::clone(&forbidden),
            no_labels,
            &field,
        );
        
        for sub in &substitutions {
            deleted.insert(*sub.from());
        }
        //println!("Entra en apply_substitution_to_map");
        linear = apply_substitution_to_map(
            constraint_storage,
            &mut non_linear_map,
            &substitutions,
            &field,
        );
        //println!("Sale de apply_substitution_to_map");
        round_id += 1;
        apply_round = !linear.is_empty();
        let _dur = now.elapsed().unwrap().as_millis();
        // //println!("Iteration no {} took {} ms", round_id, dur);
    }


    let mut apply_round_non_linear = apply_simp;
    let mut total_eliminated = 0;
    let mut linear_extracted_non_linear = 0;
    let mut linear_obtained_after_simplification = 0;
    let mut iterations_non_linear = 0;
    let mut iterations_linear = 0;
    let mut deduced_constraints = HashSet::new();

    //println!("Comienza la normalizacion.");
    //let mut non_linear_set = build_non_linear_hashset(&mut constraint_storage, &field);
    normalize_constraints(constraint_storage, &field);
    //println!("Termina la normalizacion.");
    let number_before_deduction : usize = get_number_non_empty_constraints(& constraint_storage);
    //println!("Total de constraints no lineales antes de empezar la reducción: {}",number_before_deduction);

    //println!("Comienza la creacion de clusters.");
    let mut new_clusters  = build_clusters_nonlinear(&constraint_storage);
    let mut apply_only_affected = true;
    let now = SystemTime::now();
    //println!("Termina la creacion de clusters.");
   
    while apply_round_non_linear{
        ////println!("Numero de clusters {}", new_clusters.len());
        let (substitutions, _, to_delete, num_new_linear) = non_linear_simplification(
            &mut deduced_constraints,
            new_clusters,
            Arc::clone(&forbidden),
            &field,
        );

        linear_extracted_non_linear = linear_extracted_non_linear + num_new_linear;

        ////println!("Calculadas substituciones");
        for sub in &substitutions {
            deleted.insert(*sub.from());
        }
        

        let mut linear = apply_substitution_to_map_non_linear(
            constraint_storage,
            &mut non_linear_map,
            //&mut non_linear_set,
            &substitutions,
            &field,
        );

        //let mut affected_constraints = get_affected_constraints(&constraint_storage, &non_linear_map, &substitutions);

        // //println!("------------Eliminacion no lineal---------------");
        // //println!("Numero de nuevas lineales: {}", linear.len());
        // //println!("Numero de señales eliminadas: {}", substitutions.len());

        let mut apply_round_linear = !linear.is_empty();
        apply_round_non_linear = substitutions.len() > 0|| !to_delete.is_empty();
        if substitutions.len() > 0 {
            iterations_non_linear = iterations_non_linear + 1;
        }


        while apply_round_linear {
            linear_obtained_after_simplification = linear_obtained_after_simplification + linear.len();

            let now = SystemTime::now();
            // //println!("Number of linear constraints: {}", linear.len());
            let (substitutions, _) = linear_simplification(
                linear,
                Arc::clone(&forbidden),
                no_labels,
                &field,
            );
    
            for sub in &substitutions {
                deleted.insert(*sub.from());
            }

            linear = apply_substitution_to_map_non_linear(
                constraint_storage,
               &mut non_linear_map,
               //&mut non_linear_set,
               &substitutions,
               &field,
           );

            //affected_constraints.append(&mut get_affected_constraints(&constraint_storage, &non_linear_map, &substitutions));

            total_eliminated = total_eliminated + substitutions.len();

            // //println!("------------Eliminacion lineal---------------");
            // //println!("Numero de eliminadas: {}", substitutions.len());
            // //println!("Numero de nuevas lineales: {}", linear.len());

            apply_round_linear = !linear.is_empty();
            let _dur = now.elapsed().unwrap().as_millis();

            if substitutions.len() > 0 {
                iterations_linear = iterations_linear + 1;
            }
            // //println!("Iteration no {} took {} ms", round_id, dur);
        }

        //println!("Posibles eliminaciones {:?}", to_delete.len());
        for possible_delete in to_delete{
            
            if !constraint_storage.read_constraint(possible_delete).unwrap().is_empty() {
                total_eliminated = total_eliminated + 1;
                constraint_storage.replace(possible_delete, C::empty());
            }
        }

        new_clusters = build_clusters_nonlinear(&constraint_storage);


    }

    


    println!("Total de constraints no lineales antes de empezar la reducción: {}",number_before_deduction);
    println!("--------------SIMPLIFICACION COMPLETADA----------------");    
    println!("Total de constraints eliminadas: {}", total_eliminated);
    println!("Total de lineales deducidas de no lineales: {}", linear_extracted_non_linear);
    println!("Total de lineales DISTINTAS deducidas de no lineales: {}", deduced_constraints.len());
    println!("Total de lineales obtenidas al simplificar: {}", linear_obtained_after_simplification);
    //println!("Iteraciones de deducir lineales obtenidas de no lineales: {}", iterations_non_linear);
    if total_eliminated > 0{
        let percentage : f64  = total_eliminated as f64 / number_before_deduction as f64;
        println!("Porcentaje de mejora: {}%", percentage*(100 as f64));
    }
    let dur = now.elapsed().unwrap().as_millis();
    //println!("TIME: {} ms", dur);


    remove_redundant_constraints(constraint_storage, &field);

    let _trash = constraint_storage.extract_with(&|c| C::is_empty(c));

    //println!("Numero de constraints final: {}", constraint_storage.get_no_constraints());

    let signal_map = {
        // //println!("Rebuild witness");
        let now = SystemTime::now();
        let signal_map = rebuild_witness(max_signal, deleted.clone());
        let _dur = now.elapsed().unwrap().as_millis();
        // //println!("End of rebuild witness: {} ms", dur);
        signal_map
    };
    let mut new_witness = witness.clone();
    println!("Veamos si funciono. Tam {}",new_witness.len());
    update_witness(& mut new_witness,deleted);
    println!("¡¡¡ si funciono. Tam {}",new_witness.len());

    let mut signals : HashSet<usize> = HashSet::new();
    for c_id in constraint_storage.get_ids() {
        let constraint = constraint_storage.read_constraint(c_id).unwrap();
        let signals_in_c = C::take_cloned_signals(&constraint);
        for e in signals_in_c{
            signals.insert(e);
        }
    }
    let mut toberemoved :  HashSet<usize>  = HashSet::new();
    for s in new_witness.keys(){
        if !signals.contains(s){
            toberemoved.insert(*s);
        }
    }
    for s in toberemoved{
     //   new_witness.remove(&s);
    }
    // //println!("NO CONSTANTS: {}", constraint_storage.no_constants());
    println!("Num signals in storage: {}, size witness: {}", signals.len(),new_witness.len());
    (signal_map, new_witness)
}


fn update_witness(witness : & mut BTreeMap<usize, BigInt>, deleted: HashSet<usize>) {
    for i in deleted{
        if witness.remove(&i).is_none(){ println!("Problem");}
    }
}




fn get_number_non_empty_constraints( constraint_storage : & ConstraintStorage) -> usize{
    let mut i = 0;
    for c in constraint_storage.get_ids(){
        let a = constraint_storage.read_constraint(c).unwrap();
        if !a.is_empty(){
            i = i + 1;
        }
    }
    return i;
}


//BTreemap -> en lugar de Hashmap
//Eliminar de mi witness aquellas que estén en deleted. 
