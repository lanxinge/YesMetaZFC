import YesMetaZFC.Model.Forcing.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.Model.Forcing.Functions.ValueIsomorphism
import YesMetaZFC.Model.Forcing.Maximum.UniqueRules
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 旧成员与关系的规范名称力迫

成员由规范名称的条目直接得到；关系条目由真实泛型中的规范嵌入核验，再用
有限参数反射消去外部可数性。两者均只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_mem_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b x y s t p}
    (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : M.mem p B) (hpb : Entry_d M p b R) (hxy : M.mem x y) : Mem_force_d M B R z p s t :=
  mem_force_entry_l O hZF hp (check_name_l M (check_range_l M hZF) hb hs) hb
    ((check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht s b).mpr ⟨rfl, x, hxy, hs⟩) hpb

/-- 规范名称的成员力迫在每个正条件下反射真实旧成员关系。 -/
theorem check_mem_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b x y s t p}
    (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hm : Mem_force_d M B R z p s t) : M.mem x y := by
  obtain ⟨q, a, c, hq, ha, _, he⟩ := hm.2 p (below_refl_l O hp.1 hp.2.1)
  obtain ⟨_, u, huy, hu⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht a c).mp ha
  exact (check_force_reflect_l O hZF hb hs hu (below_trans_l O hb hq hp) he).symm ▸ huy

theorem check_rel_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b F x y T s t p}
    (hb : M.mem b B) (hF : Check_d M b F T) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hxy : Entry_d M x y F) : Rel_force_d M B R z T p s t := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ₁ : Env M 7 := ((ρ₀.push F).push x).push y
  let ρ : Env M 11 := (((ρ₁.push T).push s).push t).push p
  let φ : Formula 1 3 := entry_m (.bound 1) (.bound 0) (.bound 2)
  let e : Fin 3 → Term 11 := Fin.cases (.bound 1) (Fin.cases (.bound 2) (fun _ => .bound 3))
  let α : Formula 1 11 := .conj (.mem (.bound 7) (.bound 10)) (.conj (check_m (.bound 7) (.bound 6) (.bound 3))
    (.conj (check_m (.bound 7) (.bound 5) (.bound 2)) (.conj (check_m (.bound 7) (.bound 4) (.bound 1))
      (.conj (entry_m (.bound 5) (.bound 4) (.bound 6)) (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 0) (.bound 7))))))
  have hφ : φ.FreeClosed := entry_m_freeClosed _ _ _ rfl rfl rfl
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 11) : Formula.satisfies η α ↔
      K.mem (η.bound 7) (η.bound 10) ∧ Check_d K (η.bound 7) (η.bound 6) (η.bound 3) ∧ Check_d K (η.bound 7) (η.bound 5) (η.bound 2) ∧
      Check_d K (η.bound 7) (η.bound 4) (η.bound 1) ∧ Entry_d K (η.bound 5) (η.bound 4) (η.bound 6) ∧
      Below_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 7) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE, entry_sat_l K hE, below_sat_l K hE]
    rfl
  have names : ∀ i, Name_d M B ((e i).eval ρ) :=
    Fin.cases (check_name_l M (check_range_l M hZF) hb ht)
      (Fin.cases (check_name_l M (check_range_l M hZF) hb hs) (fun _ => check_name_l M (check_range_l M hZF) hb hF))
  have hf := forces_of_generics_l φ hφ α hα e (.bound 10) (.bound 9) (.bound 8) (.bound 0)
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl rfl
    (fun K hK η O' _ _ _ hh U hU hpU ξ hξ => ?_) hZF ρ O names hp.1 hp.2.1
      ((raw M hZF.1 ρ).mpr ⟨hb, hF, hs, ht, hxy, hp⟩)
  · exact (force_entry_l hZF.1 ⟨fun i => (e i).eval ρ, ρ.free⟩ p (.bound 1) (.bound 0) (.bound 2)).mp hf
  · obtain ⟨hbB, hF', hs', ht', hxy', hp'⟩ := (raw K hK.1 η).mp hh
    have hb' := hU.upward _ _ hpU hbB hp'.2.2
    obtain ⟨f, hv, he, _⟩ := check_map_l O' hK hU hb'
    have hFv := qval_unique_l (hv _ _ hF') (hξ 2)
    have hxv := qval_unique_l (hv _ _ hs') (hξ 1)
    have hyv := qval_unique_l (hv _ _ ht') (hξ 0)
    apply (entry_sat_l _ (extension_ext_l O' hK hU) ξ (.bound 1) (.bound 0) (.bound 2)).mpr
    change Entry_d _ (ξ.bound 1) (ξ.bound 0) (ξ.bound 2)
    rw [← hFv, ← hxv, ← hyv]
    obtain ⟨v, hvp, hvF⟩ := hxy'
    exact ⟨f v, image_kpair_l f he hvp, (he _ _).mpr ⟨v, hvF, rfl⟩⟩

/-- 正条件迫使两个规范名称满足旧关系，当且仅当旧对象确实满足该关系；此处给出反射方向。 -/
theorem check_rel_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b F x y T s t p}
    (hb : M.mem b B) (hF : Check_d M b F T) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hrel : Rel_force_d M B R z T p s t) : Entry_d M x y F := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ₁ : Env M 7 := ((ρ₀.push F).push x).push y
  let ρ : Env M 11 := (((ρ₁.push T).push s).push t).push p
  let α : Formula 1 11 := .conj (.mem (.bound 7) (.bound 10)) (.conj (check_m (.bound 7) (.bound 6) (.bound 3))
    (.conj (check_m (.bound 7) (.bound 5) (.bound 2)) (.conj (check_m (.bound 7) (.bound 4) (.bound 1))
      (.conj (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 0) (.bound 7))
        (rel_force_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 0) (.bound 2) (.bound 1))))))
  let β : Formula 1 11 := entry_m (.bound 5) (.bound 4) (.bound 6)
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have hβ : β.FreeClosed := entry_m_freeClosed _ _ _ rfl rfl rfl
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 11) : Formula.satisfies η α ↔
      K.mem (η.bound 7) (η.bound 10) ∧ Check_d K (η.bound 7) (η.bound 6) (η.bound 3) ∧
      Check_d K (η.bound 7) (η.bound 5) (η.bound 2) ∧ Check_d K (η.bound 7) (η.bound 4) (η.bound 1) ∧
      Below_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 7) ∧
      Rel_force_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 3) (η.bound 0) (η.bound 2) (η.bound 1) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE,
      below_sat_l K hE, rel_force_sat_l K hE]
    rfl
  have h := source_of_generics_l α β hα hβ (.bound 10) (.bound 9) (.bound 8) (.bound 0) rfl rfl rfl rfl
    (fun K hK η O' hh U hU hpU => ?_) hZF ρ O hp.1 hp.2.1 ((raw M hZF.1 ρ).mpr ⟨hb, hF, hs, ht, hp, hrel⟩)
  · exact (entry_sat_l M hZF.1 ρ (.bound 5) (.bound 4) (.bound 6)).mp h
  · obtain ⟨hb', hF', hs', ht', hp', hr'⟩ := (raw K hK.1 η).mp hh
    have hbU := hU.upward _ _ hpU hb' hp'.2.2
    obtain ⟨e, hv, hm, hi⟩ := check_map_l O' hK hU hbU
    have he := (rel_force_truth_l O' hK hU (hv _ _ hs') (hv _ _ ht') (hv _ _ hF')).mp ⟨η.bound 0, hpU, hr'⟩
    exact (entry_sat_l K hK.1 η (.bound 5) (.bound 4) (.bound 6)).mpr
      ((image_entry_iff_l e hi hm (KP.exists_pair (ZF.modelsKP hK)) (extension_ext_l O' hK hU) _ _ _).mpr he)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地函数应用于任意名称

在决定输入旧值的分支上读取真实函数图，再混合输出规范名称。函数单值性
保证分支相容，所以整个构造只需 ZF，无须为唯一值调用选择公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def Check_app_d (M : SetTheory.Structure.{u}) (B R z b f τ σ : M.Domain) : Prop :=
  ∀ p x y s t, Below_d M B R z p b → Entry_d M x y f → Check_d M b x s → Check_d M b y t →
    Eq_force_d M B R z p τ s → Eq_force_d M B R z p σ t

def check_app_m {n} (B R z b f τ σ : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (below_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
      z.weaken.weaken.weaken.weaken.weaken (.bound 4) b.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 3) (.bound 2) f.weaken.weaken.weaken.weaken.weaken)
        (.imp (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.imp (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 2) .newest)
            (.imp (eq_force_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken.weaken (.bound 4) τ.weaken.weaken.weaken.weaken.weaken (.bound 1))
              (eq_force_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
                z.weaken.weaken.weaken.weaken.weaken (.bound 4) σ.weaken.weaken.weaken.weaken.weaken .newest))))))))))
derive_free_closed check_app_m

theorem check_app_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f τ σ : Term n) :
    Formula.satisfies ρ (check_app_m B R z b f τ σ) ↔
      Check_app_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (τ.eval ρ) (σ.eval ρ) := by
  simp only [check_app_m, Check_app_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    below_sat_l M hE, entry_sat_l M hE, check_sat_l M hE, eq_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

private theorem check_apply_mix_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b f X Y τ}
    (hb : M.mem b B)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f X Y)
    (hτ : Name_d M B τ) : ∃ σ, Name_d M B σ ∧ Check_app_d M B R z b f τ σ := by
  obtain ⟨d, hd, hdn, _⟩ := zf_check_l M hZF hb Y
  obtain ⟨W, hW⟩ := name_pool_exists_l M hZF hdn hdn
  let ρ₀ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let ρ : Env M 6 := ((ρ₀.push b).push f).push τ
  let φ : BinarySchema 6 := {
    body := .existsE (.existsE (.existsE (.conj (entry_m (.bound 2) (.bound 1) (.bound 6))
      (.conj (check_m (.bound 7) (.bound 2) .newest) (.conj (check_m (.bound 7) (.bound 1) (.bound 4))
        (.conj (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 7))
          (eq_force_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 5) .newest))))))) }
  have hφ t p : φ.denote ρ t p ↔ ∃ x y s, Entry_d M x y f ∧ Check_d M b x s ∧ Check_d M b y t ∧
      Below_d M B R z p b ∧ Eq_force_d M B R z p τ s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1, check_sat_l M hZF.1, below_sat_l M hZF.1, eq_force_sat_l M hZF.1]
    rfl
  have hn t (ht : M.mem t W) : Name_d M B t := ⟨W, ht, hW.closed⟩
  have checkn x s (hs : Check_d M b x s) := check_name_l M (check_range_l M hZF) hb hs
  obtain ⟨σ, hσ, hm⟩ := name_pool_mix_l O hZF hW φ ρ (by
    intro p q s t r hp hq hs ht hps hqt hrp hrq
    obtain ⟨x, y, a, hxy, hxa, hys, hpb, hτa⟩ := (hφ s p).mp hps
    obtain ⟨x', y', a', hxy', hxa', hyt, _, hτa'⟩ := (hφ t q).mp hqt
    have haa := eq_force_trans_l O hZF (checkn x a hxa) hτ (checkn x' a' hxa')
      (eq_force_symm_l hZF hτ (checkn x a hxa) (eq_force_lower_l O hZF hτ (checkn x a hxa) p r hp hrp hτa))
      (eq_force_lower_l O hZF hτ (checkn x' a' hxa') q r hq hrq hτa')
    have hxx := check_force_reflect_l O hZF hb hxa hxa' (below_trans_l O hb hrp hpb) haa
    subst x'
    have hyy := hf.1.2 x y y' hxy hxy'
    subst y'
    have hst := check_unique_l M hZF.1 (check_ind_l M hZF) b y s t hys hyt
    exact hst ▸ eq_force_refl_l O hZF hrp.1 (hn s hs))
  refine ⟨σ, hn σ hσ, fun p x y s t hp hxy hs ht he => ?_⟩
  have htd := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hd t b).mpr
    ⟨rfl, y, hf.output_mem_of_pairMember hxy, ht⟩
  have htW := (supp_entry_l M hW.closed hW.left htd).1
  exact hm p t hp.1 htW ((hφ t p).mpr ⟨x, y, s, hxy, hs, ht, hp, he⟩)

/-- 实际地函数作用于名称：自动构造输出名称及全部正条件上的函数值力迫。 -/
theorem check_apply_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b f X Y τ}
    (hb : M.mem b B)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f X Y)
    (hτ : Name_d M B τ) : ∃ σ c d F, Name_d M B σ ∧ Check_d M b X c ∧ Check_d M b Y d ∧ Check_d M b f F ∧
      (∀ p, Below_d M B R z p b → Mem_force_d M B R z p τ c →
        Mem_force_d M B R z p σ d ∧ Rel_force_d M B R z F p τ σ) ∧
      Check_app_d M B R z b f τ σ := by
  obtain ⟨σ, hσ, he⟩ := check_apply_mix_l O hZF hb hf hτ
  obtain ⟨c, hc, _, _⟩ := zf_check_l M hZF hb X
  obtain ⟨d, hd, hdn, _⟩ := zf_check_l M hZF hb Y
  obtain ⟨F, hF, hFn, _⟩ := zf_check_l M hZF hb f
  refine ⟨σ, c, d, F, hσ, hc, hd, hF, fun p hp hτc => ?_, he⟩
  apply (regular_conj_l (regular_mem_l O σ d) (rel_force_regular_l O hZF hFn hτ hσ)).2 p hp.1 hp.2.1
  intro q hq
  obtain ⟨r, s, a, hrq, hsa, _, hτs⟩ := hτc.2 q hq
  obtain ⟨_, x, hx, hxs⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hc s a).mp hsa
  obtain ⟨y, hy, hxy⟩ := hf.2.2 x hx
  obtain ⟨t, hyt, htn, _⟩ := zf_check_l M hZF hb y
  have hsn := check_name_l M (check_range_l M hZF) hb hxs
  have hrb := below_trans_l O hb (below_trans_l O hp.1 hrq hq) hp
  have hσt := he r x y s t hrb hxy hxs hyt hτs
  have hσd := mem_force_left_l O hZF htn hσ hdn (eq_force_symm_l hZF hσ htn hσt)
    (check_mem_force_l O hZF hb hyt hd hrq.1 hrb.2.2 hy)
  have hst := check_rel_force_l O hZF hb hF hxs hyt hrb hxy
  let φ : UnarySchema 2 := { body := rel_at_m .newest (.bound 1) (.bound 2) }
  let ρ := ord_env_l M t F
  have hτt := (force_rel_at_l M hZF.1 (ρ.push τ) r .newest (.bound 1) (.bound 2)).mp
    ((forces_name_congr_l O hZF φ ρ (Fin.cases htn (fun _ => hFn)) hsn hτ hrq.1 hrq.2.1
      (eq_force_symm_l hZF hτ hsn hτs)).mp
        ((force_rel_at_l M hZF.1 (ρ.push s) r .newest (.bound 1) (.bound 2)).mpr hst))
  let ψ : UnarySchema 2 := { body := rel_at_m (.bound 1) .newest (.bound 2) }
  let η := ord_env_l M τ F
  have hτσ := (force_rel_at_l M hZF.1 (η.push σ) r (.bound 1) .newest (.bound 2)).mp
    ((forces_name_congr_l O hZF ψ η (Fin.cases hτ (fun _ => hFn)) htn hσ hrq.1 hrq.2.1
      (eq_force_symm_l hZF hσ htn hσt)).mp
        ((force_rel_at_l M hZF.1 (η.push t) r (.bound 1) .newest (.bound 2)).mpr hτt))
  exact ⟨r, hrq, hσd, hτσ⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 旧函数的规范名字力迫

成员满覆盖的规范嵌入保留函数图。有限参数泛型判据将这个实际求值事实
转回原模型中的力迫证书，不要求原模型外部可数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z : M.Domain}

theorem check_function_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {b D X f t w s p} (hb : M.mem b B)
    (ht : Check_d M b D t) (hw : Check_d M b X w) (hs : Check_d M b f s)
    (fn : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f D X)
    (hp : Below_d M B R z p b) : Forces_d M B R z fn_body_m (fn_env_l t w s) p := by
  let ρ : Env M 11 := ⟨fun i => [B,R,z,b,D,X,f,t,w,s,p].get i,fun _ => B⟩
  let e : Fin 3 → Term 11 := Fin.cases (.bound 9) (Fin.cases (.bound 7) (fun _ => .bound 8))
  let α : Formula 1 11 := set[11] ⟪
    ⌜(.bound 3 : Term 11)⌝ₛ ∈ ⌜(.bound 0 : Term 11)⌝ₛ ∧
    ⌜check_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 7 : Term 11)⌝ₛ) ∧
    ⌜check_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ) ∧
    ⌜check_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ) ∧
    ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ) ∧
    ⌜below_m⌝ₚ(⌜(.bound 0 : Term 11)⌝ₛ,⌜(.bound 1 : Term 11)⌝ₛ,⌜(.bound 2 : Term 11)⌝ₛ,⌜(.bound 10 : Term 11)⌝ₛ,⌜(.bound 3 : Term 11)⌝ₛ)⟫
  have closed : α.FreeClosed := by simp -implicitDefEqProofs [α,Definitional.Formula.FreeClosed]
  have raw (N : Structure.{u}) (hN : N.Models ZF) (η : Env N 11) : Formula.satisfies η α ↔
      N.mem (η.bound 3) (η.bound 0) ∧ Check_d N (η.bound 3) (η.bound 4) (η.bound 7) ∧
      Check_d N (η.bound 3) (η.bound 5) (η.bound 8) ∧ Check_d N (η.bound 3) (η.bound 6) (η.bound 9) ∧
      N.IsSetFunctionFromTo (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN)))
        (η.bound 6) (η.bound 4) (η.bound 5) ∧
      Below_d N (η.bound 0) (η.bound 1) (η.bound 2) (η.bound 10) (η.bound 3) := by
    simp only [α,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,check_sat_l N hN.1,
      Formula.satisfies_isFunctionFromTo_iff (kpair_interpretation_l N hN.1 (KP.exists_pair (ZF.modelsKP hN))) hN.1,
      below_sat_l N hN.1]
    rfl
  have names : ∀ i, Name_d M B ((e i).eval ρ) := Fin.cases
    (check_name_l M (check_range_l M hZF) hb hs)
    (Fin.cases (check_name_l M (check_range_l M hZF) hb ht)
      (fun _ => check_name_l M (check_range_l M hZF) hb hw))
  have forced := forces_of_generics_l fn_body_m fn_body_closed_l α closed e
    (.bound 0) (.bound 1) (.bound 2) (.bound 10)
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl rfl
    (fun N hN η L _ _ _ hh U generic accepted ξ values => by
      obtain ⟨hb,ht,hw,hs,fn,hp⟩ := (raw N hN η).mp hh
      obtain ⟨j,checks,full,inj⟩ := check_map_l L hN generic (generic.upward _ _ accepted hb hp.2.2)
      have eqt := qval_unique_l (checks _ _ ht) (values 1)
      have eqw := qval_unique_l (checks _ _ hw) (values 2)
      have eqs := qval_unique_l (checks _ _ hs) (values 0)
      let E := extension_l N hN (η.bound 0) (η.bound 1) (η.bound 2) U
      have hE : E.Models ZF := preserves_zf_l L hN generic
      let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
      apply (Formula.satisfies_isFunctionFromTo_iff J hE.1 ξ .newest (.bound 1) (.bound 2)).mpr
      change E.IsSetFunctionFromTo J (ξ.bound 0) (ξ.bound 1) (ξ.bound 2)
      rw [← eqs,← eqt,← eqw]
      exact image_function_l j inj full fn)
    hZF ρ O names hp.1 hp.2.1 ((raw M hZF ρ).mpr ⟨hb,ht,hw,hs,fn,hp⟩)
  exact (forces_env_l hZF.1 fn_body_m fn_body_closed_l
    ⟨fun i => (e i).eval ρ,ρ.free⟩ (fn_env_l t w s) (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp forced

end YesMetaZFC.Model.Forcing.Internal

/-! ## 旧预序在规范名称下的实际力迫证书

规范嵌入的成员满性把旧载体的每个扩张元素拉回地模型，关系条目的双向保持
据此传输自反性与传递性。有限参数泛型判据消去外部可数性，只需原 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_preord_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b D V C T p}
    (hb : M.mem b B) (hC : Check_d M b D C) (hT : Check_d M b V T)
    (hV : Preord_d M D V) (hp : Below_d M B R z p b) :
    Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M C T) p := by
  let ρ : Env M 9 := ((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push D).push V).push C).push T).push p
  let e : Fin 2 → Term 9 := Fin.cases (.bound 2) (fun _ => .bound 1)
  let φ : Formula 1 2 := preord_m (.bound 0) (.bound 1)
  let α : Formula 1 9 := .conj (.mem (.bound 5) (.bound 8))
    (.conj (check_m (.bound 5) (.bound 4) (.bound 2)) (.conj (check_m (.bound 5) (.bound 3) (.bound 1))
      (.conj (preord_m (.bound 4) (.bound 3)) (below_m (.bound 8) (.bound 7) (.bound 6) (.bound 0) (.bound 5)))))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 9) : Formula.satisfies η α ↔
      K.mem (η.bound 5) (η.bound 8) ∧ Check_d K (η.bound 5) (η.bound 4) (η.bound 2) ∧
      Check_d K (η.bound 5) (η.bound 3) (η.bound 1) ∧ Preord_d K (η.bound 4) (η.bound 3) ∧
      Below_d K (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 0) (η.bound 5) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE,
      preord_sat_l hE, below_sat_l K hE]
    rfl
  have names : ∀ i, Name_d M B ((e i).eval ρ) := Fin.cases
    (check_name_l M (check_range_l M hZF) hb hC) (fun _ => check_name_l M (check_range_l M hZF) hb hT)
  have hf := forces_of_generics_l φ (preord_m_freeClosed _ _ rfl rfl) α hα e
    (.bound 8) (.bound 7) (.bound 6) (.bound 0) (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
    (fun K hK η L _ _ _ hh U hU hpU ξ hξ => ?_) hZF ρ O names hp.1 hp.2.1
      ((raw M hZF.1 ρ).mpr ⟨hb, hC, hT, hV, hp⟩)
  · exact (forces_env_l hZF.1 φ (preord_m_freeClosed _ _ rfl rfl)
      ⟨fun i => (e i).eval ρ, ρ.free⟩ (ord_env_l M C T) (Fin.cases rfl (fun _ => rfl)) p).mp hf
  · obtain ⟨hb', hC', hT', hv', hp'⟩ := (raw K hK.1 η).mp hh
    obtain ⟨f, hval, hmem, hinj⟩ := check_map_l L hK hU (hU.upward _ _ hpU hb' hp'.2.2)
    have hCv := qval_unique_l (hval _ _ hC') (hξ 0)
    have hTv := qval_unique_l (hval _ _ hT') (hξ 1)
    apply (preord_sat_l (extension_ext_l L hK hU) ξ (.bound 0) (.bound 1)).mpr
    change Preord_d _ (ξ.bound 0) (ξ.bound 1)
    rw [← hCv, ← hTv]
    have rel a b := image_entry_iff_l f hinj hmem (KP.exists_pair (ZF.modelsKP hK)) (extension_ext_l L hK hU) a b (η.bound 3)
    constructor
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem (η.bound 4) x).mp hx
      exact (rel a a).mp (hv'.1 a ha)
    · intro x y z hx hy hz hxy hyz
      obtain ⟨a, ha, rfl⟩ := (hmem (η.bound 4) x).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmem (η.bound 4) y).mp hy
      obtain ⟨c, hc, rfl⟩ := (hmem (η.bound 4) z).mp hz
      exact (rel a c).mp (hv'.2 a b c ha hb hc ((rel a b).mpr hxy) ((rel b c).mpr hyz))

end YesMetaZFC.Model.Forcing.Internal
