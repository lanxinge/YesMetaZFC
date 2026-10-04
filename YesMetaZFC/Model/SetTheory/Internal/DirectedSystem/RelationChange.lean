import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Stages

/-! # 在同一直接极限上更换关系

关系沿实际商投影拉回各纤维，原来的载体、等价类和过渡图全部复用。
这使谓词扩张能够消费同一个直接极限，而无需重新构造一套商对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_pull_l {X Y f : M.Domain} (hX : ∃ x, M.mem x X)
    (hf : M.IsSetFunctionFromTo I f X Y) (R : M.Domain) : ∃ c S, Smdl_d I c X S ∧
      ∀ x y u v, Rd_entry_d x u f → Rd_entry_d y v f → (Rd_entry_d x y S ↔ Rd_entry_d u v R) := by
  let ρ := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push R
  let φ : BinarySchema 2 := {
    body := .existsE (.existsE (.conj (rd_entry_m (.bound 3) (.bound 1) (.bound 5))
      (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m (.bound 1) .newest (.bound 4))))) }
  have sat x y : φ.denote ρ x y ↔ ∃ u v, Rd_entry_d x u f ∧ Rd_entry_d y v f ∧ Rd_entry_d u v R := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨c, S, hm, spec⟩ := smdl_exists_l I hZF φ ρ hX
  refine ⟨c, S, hm, fun x y u v hx hy => ((spec x y).trans
    (and_congr_right fun _ => and_congr_right fun _ => sat x y)).trans ?_⟩
  exact ⟨fun ⟨_, _, a, b, ha, hb, hr⟩ => hf.1.2 x a u ha hx ▸ hf.1.2 y b v hb hy ▸ hr,
    fun hr => ⟨hf.input_mem_of_pairMember hx, hf.input_mem_of_pairMember hy, u, v, hx, hy, hr⟩⟩

theorem di_relation_change_l {J L A p T R q C V c W : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V) (hm : Smdl_d I c C W) :
    ∃ S, Di_system_d J L A p T S ∧ Di_limit_d A p T S q C W ∧
      ∀ x y i E H, Rd_entry_d x i p → Rd_entry_d y i p → Rd_entry_d x E q → Rd_entry_d y H q →
        (Rd_entry_d x y S ↔ Rd_entry_d E H W) := by
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push q).push W
  let φ : BinarySchema 3 := {
    body := .existsE (.existsE (.existsE (.conj (rd_entry_m (.bound 4) (.bound 2) (.bound 7))
      (.conj (rd_entry_m (.bound 3) (.bound 2) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) (.bound 1) (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 1) .newest (.bound 5)))))))) }
  have sat x y : φ.denote ρ x y ↔ ∃ i E H, Rd_entry_d x i p ∧ Rd_entry_d y i p ∧
      Rd_entry_d x E q ∧ Rd_entry_d y H q ∧ Rd_entry_d E H W := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨S, _, spec⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have read x y i E H (hx : Rd_entry_d x i p) (hy : Rd_entry_d y i p)
      (he : Rd_entry_d x E q) (hh : Rd_entry_d y H q) : Rd_entry_d x y S ↔ Rd_entry_d E H W := by
    refine ((spec x y).trans (and_congr_right fun _ => and_congr_right fun _ => sat x y)).trans ⟨?_, ?_⟩
    · rintro ⟨_, _, _, E', H', _, _, he', hh', hr⟩
      exact (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 x E' E he' he ▸
        (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 y H' H hh' hh ▸ hr
    · exact fun hr => ⟨(h.index.bound_l hx).1, (h.index.bound_l hy).1, i, E, H, hx, hy, he, hh, hr⟩
  have system : Di_system_d J L A p T S := { h with
    locality := fun x y hxy => by
      obtain ⟨_, _, ht⟩ := (spec x y).mp hxy
      obtain ⟨i, _, _, hx, hy, _⟩ := (sat x y).mp ht
      exact ⟨i, hx, hy⟩
    relation := fun x y i u v k hx hy hu hv hxu hyv => by
      obtain ⟨E, _, he⟩ := limit.projection.2.1 x (h.index.bound_l hx).1
      obtain ⟨H, _, hh⟩ := limit.projection.2.1 y (h.index.bound_l hy).1
      obtain ⟨E', _, he'⟩ := limit.projection.2.1 u (h.index.bound_l hu).1
      obtain ⟨H', _, hh'⟩ := limit.projection.2.1 v (h.index.bound_l hv).1
      have eqE := limit.commute_l h hxu he he'
      have eqH := limit.commute_l h hyv hh hh'
      subst E' H'
      exact (read x y i E H hx hy he hh).trans (read u v k E H hu hv he' hh').symm }
  refine ⟨S, system, ⟨limit.projection, limit.range, limit.kernel, ?_, ?_, hm.2.2.1⟩, read⟩
  · intro x y E H he hh
    obtain ⟨i, u, v, hu, hv, hxu, hyv⟩ := h.common_l (limit.projection.bound_l he).1 (limit.projection.bound_l hh).1
    obtain ⟨E', _, he'⟩ := limit.projection.2.1 u (h.index.bound_l hu).1
    obtain ⟨H', _, hh'⟩ := limit.projection.2.1 v (h.index.bound_l hv).1
    have eqE := limit.commute_l h hxu he he'
    have eqH := limit.commute_l h hyv hh hh'
    exact eqE ▸ eqH ▸ (read u v i E' H' hu hv he' hh').symm.trans (system.rel_at_l hu hv hxu hyv).symm
  · intro E H hEH
    exact hm.2.2.2 E H hEH

end YesMetaZFC.SetTheory.Internal
