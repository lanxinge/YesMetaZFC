import YesMetaZFC.SetTheory.InnerModel.Separation.Formula

/-! # 有限基闭包内的 Δ₀ 分离

先构造实际原公式的真值表，再固定参数元组取纤维，最后与源集合相交。
分离集属于闭包是该构造的结论，不作为闭包定义或证明前提。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rt_tuple_closed_l (hKP : M.Models KP) {C : M.Domain} (hC : Rd_closed_d C) {n}
    (e : Fin (n + 1) → M.Domain) (he : ∀ i, M.mem (e i) C) : ∃ p, M.mem p C ∧ Rt_tuple_d e p := by
  induction n with
  | zero => exact ⟨e 0, he 0, rfl⟩
  | succ n ih =>
    obtain ⟨q, hqC, hq⟩ := ih (fun i => e i.succ) (fun i => he i.succ)
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total (e 0) q
    exact ⟨p, hC .opair (e 0) q q (he 0) hqC hqC p (rd_opair_value_l hKP.1 hp), q, hp, hq⟩

theorem rd_separation_l (hKP : M.Models KP) {C U : M.Domain} (hC : Rd_closed_d C)
    (ht : M.TransitiveSet C) (hU : M.mem U C) (hu : M.TransitiveSet U)
    {n} (φ : Delta0UnarySchema n) (ρ : Env M n) (hρ : ∀ i, M.mem (ρ.bound i) U)
    {X : M.Domain} (hX : M.mem X U) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ φ.toUnarySchema.denote ρ x := by
  let hn : Nonempty {x : M.Domain // M.mem x U} := ⟨⟨X, hX⟩⟩
  let e : Rt_env U n := fun i => if h : i.val < n then ⟨ρ.bound ⟨i.val, h⟩, hρ _⟩ else ⟨X, hX⟩
  have he i : (e i.castSucc).val = ρ.bound i := by
    change (if h : i.val < n then (⟨ρ.bound ⟨i.val, h⟩, hρ _⟩ : {x : M.Domain // M.mem x U}) else ⟨X, hX⟩).val = _
    rw [dif_pos i.isLt]
  have hφ (x : (rt_model_l U hn).Domain) :
      Formula.satisfies (rt_env_l hn (Fin.cases x e)) φ.body ↔ φ.toUnarySchema.denote ρ x.val := by
    apply (rt_model_delta_l hu hn φ.delta0 _).trans
    apply Formula.closed_env_l _ φ.freeClosed
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact he j
  obtain ⟨R, hRC, hR⟩ := rt_formula_l hKP hC hU hu hn φ.body φ.freeClosed
  obtain ⟨q, hqC, hq⟩ := rt_tuple_closed_l hKP hC (fun i => (e i).val)
    (fun i => ht U hU _ (e i).property)
  obtain ⟨S, hSC, hS⟩ := hC.exists_l hKP .fiber hRC hqC hqC
  have hs x : M.mem x S ↔ M.mem x U ∧ φ.toUnarySchema.denote ρ x := by
    rw [hS x]
    change Rd_entry_d x q R ↔ _
    constructor
    · rintro ⟨p, hp, hpR⟩
      obtain ⟨f, ⟨r, hr, hf⟩, hfp⟩ := (hR p).mp hpR
      obtain ⟨hx, hqr⟩ := kpair_injective_l M hp hr
      subst r
      have hf' := rt_env_inj_l hf hq
      have hf'' : f = Fin.cases (f 0) e := by
        funext i
        exact Fin.cases rfl (congrFun hf') i
      have hp' := (hφ (f 0)).mp (hf'' ▸ hfp)
      exact hx.symm ▸ ⟨(f 0).property, hp'⟩
    · rintro ⟨hx, hp⟩
      obtain ⟨p, hpq⟩ := (kp_pair_l hKP).total x q
      let f : Rt_env U (n + 1) := Fin.cases ⟨x, hx⟩ e
      exact ⟨p, hpq, (hR p).mpr ⟨f, ⟨q, hpq, hq⟩, (hφ ⟨x, hx⟩).mpr hp⟩⟩
  have hXC := ht U hU X hX
  obtain ⟨D, hDC, hD⟩ := hC.exists_l hKP .diff hXC hSC hXC
  obtain ⟨Y, hYC, hY⟩ := hC.exists_l hKP .diff hXC hDC hXC
  refine ⟨Y, hYC, fun x => ?_⟩
  rw [hY x]; change (M.mem x X ∧ ¬ M.mem x D) ↔ _
  rw [hD x]; change (M.mem x X ∧ ¬ (M.mem x X ∧ ¬ M.mem x S)) ↔ _
  rw [hs x]
  exact ⟨fun ⟨hx, hn⟩ => ⟨hx, (Classical.byContradiction (fun h => hn ⟨hx, h⟩)).2⟩,
    fun ⟨hx, hp⟩ => ⟨hx, fun h => h.2 ⟨hu X hX x hx, hp⟩⟩⟩

end YesMetaZFC.SetTheory.InnerModel
