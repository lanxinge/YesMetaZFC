import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedNormal
import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 坍塌把坐标类精确识别为支撑序数

坐标原子给出全部已知前驱，正规性排除额外前驱。对实际原公式作成员
归纳，得到每个坐标类的坍塌值；不借助产生扩展器的旧嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_seed_collapse_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q C W N e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
    (hωL : M.MemberSubset ω L) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (h : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (collapse : Wc_graph_d C W e) (he : Fn0_d C N e) :
    M.MemberSubset L N ∧ ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 4 := ⟨Fin.cases κ (Fin.cases L (Fin.cases q (fun _ => e))), fun _ => L⟩
  let φ : UnarySchema 4 := {
    body := .forallE (.imp (ep_seed_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest)
      (rd_entry_m .newest (.bound 1) (.bound 5))) }
  have sat α : φ.denote ρ α ↔ ∀ E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ep_seed_sat_l hZF.1, rd_entry_sat_l hZF.1]; rfl
  have fixed : ∀ α E, Ep_seed_d κ L q α E → Rd_entry_d E α e := by
    intro α
    apply (sat α).mp (ZF.mem_ind_l M hZF I φ ρ ?_ α)
    intro α ih
    apply (sat α).mpr
    intro E seed
    have bounds : M.mem α L ∧ M.mem E C := by
      obtain ⟨_, a, i, _, _, ha, hi, _, _, u, B, _, _, hu⟩ := seed
      exact ⟨(ha.bound_l hi).2, (limit.projection.bound_l hu).2⟩
    obtain ⟨y, _, hEy⟩ := he.2.1 E bounds.2
    have eq : y = α := hZF.1.eq_of_same_members y α fun β => by
      rw [(collapse.2 E y hEy).2.2 β]
      constructor
      · rintro ⟨H, _, hHE, hHβ⟩
        obtain ⟨γ, hγα, seedH⟩ := ep_seed_down_l hZF source hκ hωL family coherent normal h limit seed hHE
        have hHγ := (sat γ).mp (ih γ hγα) H seedH
        exact (fn0_function_l (ZF.modelsKP hZF) he).1.2 H γ β hHγ hHβ ▸ hγα
      · intro hβα
        obtain ⟨H, hHC, seedH⟩ := ep_seed_exists_l hZF source family h limit (hL α bounds.1 β hβα)
        exact ⟨H, hHC, (ep_seed_atoms_l hZF source family atoms h limit seedH seed).2.mpr hβα,
          (sat β).mp (ih β hβα) H seedH⟩
    exact eq ▸ hEy
  exact ⟨fun α hα => by
    obtain ⟨E, _, hs⟩ := ep_seed_exists_l hZF source family h limit hα
    exact (he.bound_l (fixed α E hs)).2, fixed⟩

end YesMetaZFC.SetTheory.LargeCardinal
