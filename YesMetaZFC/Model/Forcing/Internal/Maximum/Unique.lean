import YesMetaZFC.Model.Forcing.Internal.Maximum.WitnessPool
import YesMetaZFC.Model.Forcing.Internal.Maximum.UniqueRules
import YesMetaZFC.Model.Forcing.Internal.Maximum.Mixing
import YesMetaZFC.Model.Forcing.Internal.Maximum.Normal

/-! # 原 ZF 中的唯一见证名称装配

原收集模式给出局部见证池。唯一性使条件交叠处的见证被迫相等，故直接混合
整个见证池，再取规范代表；不需要极大反链选择或选择公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 原存在与唯一性公式在所有正条件成立时，自动产生唯一的规范见证名称。 -/
theorem unique_maximum_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i))
    (hEx : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z (.existsE φ.body) ρ p)
    (hUn : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z (unique_m φ) ρ p) :
    ∃ t, Name_d M B t ∧ Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t t ∧
      (∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push t) p) ∧
      ∀ u, Name_d M B u →
        Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z u u →
        (∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push u) p) → u = t := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hen := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B e he
  let η : Env M n := ⟨ρ.bound, fun _ => e⟩
  have push s (hs : Name_d M B s) : ∀ v : Term (n+1), Name_d M B (v.eval (η.push s)) := by
    intro v
    cases v with
    | free _ => exact hen
    | bound i => exact Fin.cases hs hρ i
  have ex p hp hz := (forces_env_l hZF.1 (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) ρ η (fun _ => rfl) p).mp (hEx p hp hz)
  have un p hp hz := (forces_env_l hZF.1 _ (unique_closed_l φ) ρ η (fun _ => rfl) p).mp (hUn p hp hz)
  obtain ⟨A, hA, hSound, hPool⟩ := witness_pool_l (B := B) (R := R) (z := z) hZF φ η
  obtain ⟨W, hAW, hW⟩ := hA
  let δ := ((η.push B).push R).push z
  let es : Fin n → Term (n+5) := fun i => .bound ⟨i.val+5, by omega⟩
  have hδ a b : (⟨fun i => (es i).eval ((δ.push a).push b), ((δ.push a).push b).free⟩ : Env M n) = η := by
    cases ρ; rfl
  let χ : BinarySchema (n+3) := {
    body := force_at_m φ.body (Fin.cases (.bound 1) es) (.bound 4) (.bound 3) (.bound 2) .newest
    freeClosed := force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl }
  have hχ s p : χ.denote δ s p ↔ Forces_d M B R z φ.body (η.push s) p := by
    simp only [BinarySchema.denote, χ, force_at_sat_l, args_cons_l, hδ]
    rfl
  obtain ⟨s, hs, _, hMix⟩ := mixing_l O hZF χ δ hW (by
    intro p q s t r hp hq hs ht hsp htq hrp hrq
    have hsN : Name_d M B s := ⟨W, hs, hW⟩
    have htN : Name_d M B t := ⟨W, ht, hW⟩
    exact forced_unique_l O hZF φ η hρ hsN htN hrp.1 hrp.2.1 (un r hrp.1 hrp.2.1)
      ((forces_regular_l O hZF φ.body (η.push s) (push s hsN)).1 p r hp hrp ((hχ s p).mp hsp))
      ((forces_regular_l O hZF φ.body (η.push t) (push t htN)).1 q r hq hrq ((hχ t q).mp htq)))
  have hsφ p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z φ.body (η.push s) p := by
    apply (forces_regular_l O hZF φ.body (η.push s) (push s hs)).2 p hp hz
    intro q hq
    obtain ⟨r, hr, v, hv, hφ⟩ := forces_exists_dense_l hZF.1 (ex p hp hz) q hq
    obtain ⟨u, hu⟩ := hPool r hr.1 v hv hφ
    have huW := (supp_entry_l M hW hAW hu).1
    have heq := hMix r u hr.1 huW ((hχ u r).mpr (hSound u r hu))
    exact ⟨r, hr, (forces_name_congr_l O hZF φ η hρ hs ⟨W, huW, hW⟩ hr.1 hr.2.1 heq).mpr (hSound u r hu)⟩
  obtain ⟨t, _, htNorm, ht, hts⟩ := norm_name_exists_l O hZF hs
  have htφ p (hp : M.mem p B) (hz : p ≠ z) : Forces_d M B R z φ.body (ρ.push t) p :=
    (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).mpr
      ((forces_name_congr_l O hZF φ η hρ ht hs hp hz (hts p hp hz)).mpr (hsφ p hp hz))
  refine ⟨t, ht, htNorm, htφ, fun u hu huNorm huφ => ?_⟩
  exact norm_name_congr_l O hZF hu ht
    (fun p hp hz => forced_unique_l O hZF φ ρ hρ hu ht hp hz (hUn p hp hz) (huφ p hp hz) (htφ p hp hz)) huNorm htNorm

end YesMetaZFC.Model.Forcing.Internal
