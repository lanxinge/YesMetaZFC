import YesMetaZFC.Model.Forcing.Internal.Names.Construction

/-! # 内部名称扩张的全收集模式

在“源子名称 × 条件集”上，内部收集为每个能够力迫见证的条件选取一个名称。
无见证的输入用空名称处理；随后分离有效名称并统一加上一个被接受的标签。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)

local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem internal_collection_l {n} (φ : BinarySchema n) (η : Env E n) (A : (E).Domain)
    (h : ∀ x : (E).Domain, x ∈ A → ∃ y : (E).Domain,
      Formula.satisfies ((η.push x).push y) φ.body) :
    ∃ C : (E).Domain, ∀ x : (E).Domain, x ∈ A → ∃ y : (E).Domain,
      y ∈ C ∧ Formula.satisfies ((η.push x).push y) φ.body := by
  classical
  obtain ⟨ρ, hρ⟩ := lift_env_l hZF η
  obtain ⟨t, ht, hA⟩ := value_name_l A
  obtain ⟨S, htS, hS⟩ := ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨K, hK⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let δ := ((ρ.push B).push R).push z
  let es : Fin n → Term (n + 7) := fun i => .bound ⟨i.val + 7, by omega⟩
  let χ : UnarySchema (n+1) := { body := φ.body, freeClosed := φ.freeClosed }
  let ψ : BinarySchema (n + 3) := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 3) (.bound 1) .newest)
      (witness_m χ (Fin.cases (.bound 1) es) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 2))))
    freeClosed := by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, es]
      apply witness_closed_l
      · exact Fin.cases rfl (fun _ => rfl)
      all_goals rfl }
  have hψ k v : ψ.denote δ k v ↔ ∃ a p, KPair_d M k a p ∧ Name_d M B v ∧
      ∀ w, Name_d M B w → Forces_d M B R z φ.body ((ρ.push a).push w) p →
        Forces_d M B R z φ.body ((ρ.push a).push v) p := by
    have hs a p : (⟨fun i => (es i).eval ((((δ.push k).push v).push a).push p),
        ((((δ.push k).push v).push a).push p).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, witness_sat_l hZF.1, args_cons_l, hs]
    rfl
  obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF ψ δ K (fun k hk => by
    obtain ⟨a, _, p, _, hk⟩ := (hK k).mp hk
    by_cases h : ∃ v, Name_d M B v ∧ Forces_d M B R z φ.body ((ρ.push a).push v) p
    · obtain ⟨v, hv, hφ⟩ := h
      exact ⟨v, (hψ k v).mpr ⟨a, p, hk, hv, fun _ _ _ => hφ⟩⟩
    · exact ⟨e, (hψ k e).mpr ⟨a, p, hk, hen, fun v hv hφ => False.elim (h ⟨v, hv, hφ⟩)⟩⟩)
  let ρB : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let ν : UnarySchema 1 := { body := name_m (.bound 1) (.bound 0) }
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF ν ρB T
  have hf v : M.mem v F ↔ M.mem v T ∧ Name_d M B v :=
    (hF v).trans (and_congr_right fun _ => name_sat_l M hZF.1 (ρB.push v) (.bound 1) (.bound 0))
  obtain ⟨b, hb⟩ := hU.inhabited
  let ρb : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  obtain ⟨q, hq, _, hqE⟩ := name_comp_l M hZF BinarySchema.constantValue ρb B F
    (fun v hv => ((hf v).mp hv).2)
  obtain ⟨C, hC⟩ := name_value_l (R := R) (z := z) (U := U) hq
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨a, c, ha, hc, hax⟩ := (qval_mem_l O hZF hU hA).mp hx
  obtain ⟨y, hxy⟩ := h x hx
  obtain ⟨v, hv, hvy⟩ := value_name_l y
  have hρ' := env_val_push_l hZF (env_val_push_l hZF hρ hax) hvy
  have hEval := formula_eval_l O hZF hU φ.body φ.freeClosed ((ρ.push a).push v)
    ((η.push x).push y) hρ'
  obtain ⟨p, hp, hpφ⟩ := hEval.2.mpr hxy
  obtain ⟨r, hr, _, hrp⟩ := hU.directed c p hc hp
  have hr' := hU.proper r hr
  have hrφ := hEval.1.1 p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hpφ
  obtain ⟨k, hk⟩ := I.total a r
  obtain ⟨w, hwT, hw⟩ := hT k ((hK k).mpr ⟨a, (supp_entry_l M hS htS ha).1, r, hr'.1, hk⟩)
  obtain ⟨a', r', hk', hwN, hwφ⟩ := (hψ k w).mp hw
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hk hk'
  obtain ⟨y', hwy⟩ := name_value_l (R := R) (z := z) (U := U) hwN
  refine ⟨y', (qval_mem_l O hZF hU hC).mpr ⟨w, b, (hqE w b).mpr ⟨(hf w).mpr ⟨hwT, hwN⟩,
    (hU.proper b hb).1, (Formula.denote_constantValue_iff hZF.1 ρb w b).mpr rfl⟩, hb, hwy⟩, ?_⟩
  exact (forcing_truth_l O hZF hU φ.body φ.freeClosed ((ρ.push a).push w)
    ((η.push x).push y') (env_val_push_l hZF (env_val_push_l hZF hρ hax) hwy)).mp
      ⟨r, hr, hwφ v hv hrφ⟩

end YesMetaZFC.Model.Forcing.Internal
