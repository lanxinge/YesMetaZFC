import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Stages

/-! # 任意内部有限赋值可以放入共同分量

在原公式上归纳，把有限多个类推到共同分量。该分量上的投影为单射，
所以代表随后由唯一值收集构造；全程只需 ZF，不选择可数代表族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_finite_cover_l (hZF : M.Models ZF) {ω J L A p T R q C V b f : M.Domain}
    (hω : M.IsOmega ω) (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (hb : M.mem b ω) (hf : Fn0_d ω C f) : ∃ i c X S a,
      Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S ∧ Fn0_d ω X a ∧
      ∀ j x B, M.mem j b → Rd_entry_d j x a → Rd_entry_d j B f → Rd_entry_d x B q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have push {x i j B} (hxi : Rd_entry_d x i p) (hij : Rd_entry_d i j L) (hxB : Rd_entry_d x B q) :
      ∃ y, Rd_entry_d y j p ∧ Rd_entry_d y B q := by
    obtain ⟨y, hyj, hxy⟩ := h.total x i j hxi hij
    obtain ⟨E, _, hyE⟩ := limit.projection.2.1 y (h.bound x y hxy).2
    exact ⟨y, hyj, (limit.commute_l h hxy hxB hyE).symm ▸ hyE⟩
  obtain ⟨z, _, hzω⟩ := hω.1.1
  obtain ⟨B₀, hB₀, _⟩ := hf.2.1 z hzω
  obtain ⟨x₀, hx₀⟩ := (limit.range B₀).mp hB₀
  obtain ⟨i₀, hi₀, hx₀i⟩ := h.index.2.1 x₀ (limit.projection.bound_l hx₀).1
  let ρ : Env M 6 := ⟨Fin.cases J (Fin.cases p (Fin.cases q (Fin.cases f (Fin.cases L (fun _ => i₀))))), fun _ => f⟩
  let φ : UnarySchema 6 := {
    body := Formula.existsMem (.bound 1) (.conj (rd_entry_m (.bound 7) .newest (.bound 6)) (Formula.forallMem (.bound 1)
      (.forallE (.imp (rd_entry_m (.bound 1) .newest (.bound 7)) (.existsE
        (.conj (rd_entry_m .newest (.bound 3) (.bound 6)) (rd_entry_m .newest (.bound 1) (.bound 7)))))))) }
  have sat n : φ.denote ρ n ↔ ∃ i, M.mem i J ∧ Rd_entry_d i₀ i L ∧
      ∀ j, M.mem j n → ∀ B, Rd_entry_d j B f → ∃ x, Rd_entry_d x i p ∧ Rd_entry_d x B q := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · exact fun e he => (sat e).mpr ⟨i₀, hi₀, h.order.refl i₀ hi₀, fun j hj => (he j hj).elim⟩
    · intro n hn ih m hs
      obtain ⟨i, hi, h₀i, bound⟩ := (sat n).mp ih
      obtain ⟨B, hB, hnB⟩ := hf.2.1 n hn
      obtain ⟨x, hxB⟩ := (limit.range B).mp hB
      obtain ⟨j, hj, hxj⟩ := h.index.2.1 x (limit.projection.bound_l hxB).1
      obtain ⟨k, hk, hik, hjk⟩ := h.order.directed i j hi hj
      refine (sat m).mpr ⟨k, hk, h.order.trans i₀ i k h₀i hik, fun a ha E haE => ?_⟩
      rcases (hs a).mp ha with ha | ha
      · obtain ⟨y, hyi, hyE⟩ := bound a ha E haE
        exact push hyi hik hyE
      · have ea := hZF.1.eq_of_same_members a n ha
        have eB := hf.2.2 n hn B hB E (hf.bound_l haE).2 hnB (ea ▸ haE)
        exact eB ▸ push hxj hjk hxB
  obtain ⟨i, _, h₀i, bound⟩ := (sat b).mp (all b hb)
  obtain ⟨w, hwi, _⟩ := push hx₀i h₀i hx₀
  obtain ⟨c, X, S, stage⟩ := di_stage_exists_l hZF h hwi
  have hwX := (stage.2.1 w).mpr ⟨(h.index.bound_l hwi).1, hwi⟩
  let η : Env M 5 := ⟨Fin.cases X (Fin.cases b (Fin.cases f (Fin.cases q (fun _ => w)))), fun _ => f⟩
  let ψ : BinarySchema 5 := {
    body := .conj (.mem .newest (.bound 2)) (.disj (.conj (.mem (.bound 1) (.bound 3)) (.existsE
      (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m (.bound 1) .newest (.bound 6)))))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 6)))) }
  have read j y : ψ.denote η j y ↔ M.mem y X ∧
      ((M.mem j b ∧ ∃ B, Rd_entry_d j B f ∧ Rd_entry_d y B q) ∨ (¬ M.mem j b ∧ y = w)) := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have total j (hj : M.mem j ω) : ∃ y, ψ.denote η j y := by
    classical
    by_cases hjb : M.mem j b
    · obtain ⟨B, _, hjB⟩ := hf.2.1 j hj
      obtain ⟨x, hxi, hxB⟩ := bound j hjb B hjB
      exact ⟨x, (read j x).mpr ⟨(stage.2.1 x).mpr ⟨(h.index.bound_l hxi).1, hxi⟩, Or.inl ⟨hjb, B, hjB, hxB⟩⟩⟩
    · exact ⟨w, (read j w).mpr ⟨hwX, Or.inr ⟨hjb, rfl⟩⟩⟩
  have unique j (hj : M.mem j ω) x y (hx : ψ.denote η j x) (hy : ψ.denote η j y) : x = y := by
    obtain ⟨hxX, hx⟩ := (read j x).mp hx
    obtain ⟨hyX, hy⟩ := (read j y).mp hy
    rcases hx with ⟨hb, B, hjB, hxB⟩ | ⟨hb, rfl⟩ <;>
      rcases hy with ⟨hb', E, hjE, hyE⟩ | ⟨hb', rfl⟩
    · exact (h.eq_at_l ((stage.2.1 x).mp hxX).2 ((stage.2.1 y).mp hyX).2).mp
        ((limit.kernel x y B E hxB hyE).mp (hf.2.2 j hj B (hf.bound_l hjB).2 E (hf.bound_l hjE).2 hjB hjE))
    · exact (hb' hb).elim
    · exact (hb hb').elim
    · rfl
  obtain ⟨a, ha, select⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η total unique
    (fun j y _ hy => ((read j y).mp hy).1)
  refine ⟨i, c, X, S, a, stage, fn0_of_function_l (ZF.modelsKP hZF) ha, fun j y B hj hy hjB => ?_⟩
  rcases ((read j y).mp ((select j y).mp hy).2).2 with ⟨_, E, hjE, hyE⟩ | ⟨hn, _⟩
  · exact hf.2.2 j (hω.transitive hZF b hb j hj) E (hf.bound_l hjE).2 B (hf.bound_l hjB).2 hjE hjB ▸ hyE
  · exact (hn hj).elim

end YesMetaZFC.SetTheory.Internal
