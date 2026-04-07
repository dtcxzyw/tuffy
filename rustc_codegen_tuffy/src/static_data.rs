use rustc_middle::mir::interpret::GlobalAlloc;
use rustc_middle::ty::{Instance, TyCtxt};
use tuffy_target::reloc::{RelocKind, Relocation};
use tuffy_target::types::StaticData;

use crate::mir_to_ir;

/// Extract relocations from an allocation, emitting nested memory
/// allocations as additional `StaticData` entries.
pub(crate) fn collect_alloc_relocs<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc: &rustc_middle::mir::interpret::Allocation,
    static_data: &mut Vec<StaticData>,
    referenced_instances: &mut Vec<Instance<'tcx>>,
    data_counter: &mut u64,
    vtable_cache: &mut mir_to_ir::VtableCache,
) -> Vec<Relocation> {
    let mut relocs = Vec::new();
    for (offset, prov) in alloc.provenance().ptrs().iter() {
        let rel_offset = offset.bytes() as usize;
        let alloc_id = prov.alloc_id();
        let sym = match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance } => {
                referenced_instances.push(instance);
                tcx.symbol_name(instance).name.to_string()
            }
            GlobalAlloc::Static(def_id) => {
                let inst = Instance::mono(tcx, def_id);
                tcx.symbol_name(inst).name.to_string()
            }
            GlobalAlloc::Memory(nested) => {
                let inner = nested.inner();
                let bytes = inner
                    .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                    .to_vec();
                let name = next_static_name(data_counter, ".Lstatic");
                let nested_relocs = collect_alloc_relocs(
                    tcx,
                    inner,
                    static_data,
                    referenced_instances,
                    data_counter,
                    vtable_cache,
                );
                static_data.push(StaticData {
                    name: name.clone(),
                    data: bytes,
                    relocations: nested_relocs,
                    writable: false,
                    used: false,
                    weak_undefined: false,
                    align: inner.align.bytes(),
                    thread_local: false,
                });
                name
            }
            GlobalAlloc::VTable(ty, trait_ref) => {
                let principal = trait_ref
                    .principal()
                    .map(|principal| principal.skip_binder());
                if let Ok(vtable_id) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        tcx.vtable_allocation((ty, principal))
                    }))
                {
                    if let Some(existing_name) = vtable_cache.get(&vtable_id) {
                        existing_name.clone()
                    } else if let GlobalAlloc::Memory(vtable_alloc) = tcx.global_alloc(vtable_id) {
                        let inner = vtable_alloc.inner();
                        let bytes = inner
                            .inspect_with_uninit_and_ptr_outside_interpreter(0..inner.len())
                            .to_vec();
                        let name = next_static_name(data_counter, ".Lvtable");
                        vtable_cache.insert(vtable_id, name.clone());
                        let nested_relocs = collect_alloc_relocs(
                            tcx,
                            inner,
                            static_data,
                            referenced_instances,
                            data_counter,
                            vtable_cache,
                        );
                        static_data.push(StaticData {
                            name: name.clone(),
                            data: bytes,
                            relocations: nested_relocs,
                            writable: false,
                            used: false,
                            weak_undefined: false,
                            align: inner.align.bytes(),
                            thread_local: false,
                        });
                        name
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
            }
            GlobalAlloc::TypeId { .. } => continue,
        };
        relocs.push(Relocation {
            offset: rel_offset,
            symbol: sym,
            kind: RelocKind::Abs64,
        });
    }
    relocs
}

fn next_static_name(data_counter: &mut u64, prefix: &str) -> String {
    format!("{prefix}.{}", {
        let id = *data_counter;
        *data_counter += 1;
        id
    })
}
