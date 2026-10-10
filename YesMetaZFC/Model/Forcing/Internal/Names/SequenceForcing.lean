import YesMetaZFC.Model.Forcing.Internal.Names.Sequence
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.Model.Forcing.Internal.Functions.Rules

/-! # 实际名称序列的同条件坐标读取

内部函数图的每个条目，在装配名称中以规范索引为输入；证明只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem nseq_entry_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b f t i s c p}
    (hb : M.mem b B) (ht : Nseq_d M B b f t) (hic : Check_d M b i c)
    (hs : Name_d M B s) (his : Entry_d M i s f) (hp : Below_d M B R z p b) :
    Rel_force_d M B R z t p c s := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ : Env M 10 := (((((ρ₀.push f).push t).push i).push s).push c).push p
  let φ : Formula 1 3 := entry_m (.bound 1) .newest (.bound 2)
  let e : Fin 3 → Term 10 := Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .bound 4))
  let α : Formula 1 10 := .conj (.mem (.bound 6) (.bound 9))
    (.conj (below_m (.bound 9) (.bound 8) (.bound 7) .newest (.bound 6))
      (.conj (nseq_m (.bound 9) (.bound 6) (.bound 5) (.bound 4))
        (.conj (check_m (.bound 6) (.bound 3) (.bound 1)) (entry_m (.bound 3) (.bound 2) (.bound 5)))))
  have raw (N : SetTheory.Structure.{u}) (hE : Extensional N) (η : Env N 10) : Formula.satisfies η α ↔
      N.mem (η.bound 6) (η.bound 9) ∧ Below_d N (η.bound 9) (η.bound 8) (η.bound 7) (η.bound 0) (η.bound 6) ∧
      Nseq_d N (η.bound 9) (η.bound 6) (η.bound 5) (η.bound 4) ∧
      Check_d N (η.bound 6) (η.bound 3) (η.bound 1) ∧ Entry_d N (η.bound 3) (η.bound 2) (η.bound 5) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, below_sat_l N hE,
      nseq_sat_l N hE, check_sat_l N hE, entry_sat_l N hE]
    rfl
  have hh := forces_of_generics_l φ (entry_m_freeClosed _ _ _ rfl rfl rfl) α
    (by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]) e (.bound 9) (.bound 8) (.bound 7) .newest
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl rfl
    (fun N hN η L _ _ _ ha U hU hpU ξ hξ => ?_) hZF ρ O
      (Fin.cases hs (Fin.cases (check_name_l M (check_range_l M hZF) hb hic) (fun _ => ht.1))) hp.1 hp.2.1
      ((raw M hZF.1 ρ).mpr ⟨hb, hp, ht, hic, his⟩)
  · exact (force_entry_l hZF.1 (⟨fun i => (e i).eval ρ, ρ.free⟩ : Env M 3)
      p (.bound 1) .newest (.bound 2)).mp hh
  · obtain ⟨hb', hp', ht', hc', his'⟩ := (raw N hN.1 η).mp ha
    obtain ⟨j, hv, _, _⟩ := check_map_l L hN hU (hU.upward _ _ hpU hb' hp'.2.2)
    have hci := qval_unique_l (hv _ _ hc') (hξ 1)
    exact (entry_sat_l _ (extension_ext_l L hN hU) ξ (.bound 1) .newest (.bound 2)).mpr
      (((nseq_value_l L hN hU hb' ht' (hξ 2) j hv).2 _ _).mpr ⟨_, _, his', hci, hξ 0⟩)

end YesMetaZFC.Model.Forcing.Internal
