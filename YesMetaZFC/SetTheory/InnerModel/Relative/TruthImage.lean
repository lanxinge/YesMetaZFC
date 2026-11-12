import YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax
import YesMetaZFC.Model.SetTheory.Embedding.Reflect
import YesMetaZFC.SetTheory.Descriptive.Topology.Completion

/-! # 函数实数族的传递种子沿成员满嵌入保持

非空的 D→D 函数族在 D 传递时，只需两次并与 D 即得到 TC({B})。
有限层的显式成员方程使种子向外绝对；不使用源模型的外部良基性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

/-- 对实际函数实数族，原最小传递种子的像仍是目标中的最小传递种子。 -/
theorem real_tc_image_l (hM : M.Models KP) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
    {D B S : M.Domain} (trans : M.TransitiveSet D)
    (reals : ∀ x, M.mem x B → Fn0_d D D x) (ne : ∃ x, M.mem x B) (tc : Tc_d B S) : Tc_d (e B) (e S) := by
  obtain ⟨U,V,T,un,un',seed⟩ := rf_seed_exists_l hM D B
  have eq := tc_unique_l hM.1 tc (rf_seed_l trans reals ne un un' seed)
  subst T
  have union {B U} (un : ∀ x, M.mem x U ↔ ∃ y, M.mem y B ∧ M.mem x y) :
      ∀ x, N.mem x (e U) ↔ ∃ y, N.mem y (e B) ∧ N.mem x y := by
    intro x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := (full U x).mp hx
      obtain ⟨b,hb,ab⟩ := (un a).mp ha
      exact ⟨e b,(image_member_l e inj full).mpr hb,(image_member_l e inj full).mpr ab⟩
    · rintro ⟨y,hy,xy⟩
      obtain ⟨b,hb,rfl⟩ := (full B y).mp hy
      obtain ⟨a,ab,rfl⟩ := (full b x).mp xy
      exact (image_member_l e inj full).mpr ((un a).mpr ⟨b,hb,ab⟩)
  apply rf_seed_l (image_transitive_l e full trans) (fun x hx => ?_) (ne.elim fun x hx => ⟨e x,(image_member_l e inj full).mpr hx⟩)
    (union un) (union un')
  · intro x
    rw [full S x]
    constructor
    · rintro ⟨a,ha,rfl⟩
      rcases (seed a).mp ha with rfl | ha | ha | ha | ha
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ((image_member_l e inj full).mpr ha))
      · exact Or.inr (Or.inr (Or.inl ((image_member_l e inj full).mpr ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((image_member_l e inj full).mpr ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ((image_member_l e inj full).mpr ha))))
    · rintro (rfl | hx | hx | hx | hx)
      · exact ⟨B,(seed B).mpr (Or.inl rfl),rfl⟩
      · obtain ⟨a,ha,eq⟩ := (full B x).mp hx
        exact ⟨a,(seed a).mpr (Or.inr (Or.inl ha)),eq⟩
      · obtain ⟨a,ha,eq⟩ := (full U x).mp hx
        exact ⟨a,(seed a).mpr (Or.inr (Or.inr (Or.inl ha))),eq⟩
      · obtain ⟨a,ha,eq⟩ := (full V x).mp hx
        exact ⟨a,(seed a).mpr (Or.inr (Or.inr (Or.inr (Or.inl ha)))),eq⟩
      · obtain ⟨a,ha,eq⟩ := (full D x).mp hx
        exact ⟨a,(seed a).mpr (Or.inr (Or.inr (Or.inr (Or.inr ha)))),eq⟩
  · obtain ⟨a,ha,rfl⟩ := (full B x).mp hx
    let ρ : Env M 3 := ⟨fun k => [D,D,a].get k,fun _ => a⟩
    exact (fn0_sat_l hN (image_env_l e ρ) (.bound 0) (.bound 1) (.bound 2)).mp
      ((delta0_image_l e inj full (fn0_delta_l (.bound 0) (.bound 1) (.bound 2)) ρ).mp
        ((fn0_sat_l hM.1 ρ (.bound 0) (.bound 1) (.bound 2)).mpr (reals a ha)))

end YesMetaZFC.SetTheory.InnerModel.Relative

/-! ## 原派生模型断言向弱目标的公式运输

保留原传递种子及层中同一见证。种子的有限成员方程、层的实际 Σ₁
递归证书和见证集合上的满同构共同给出原公式真值；目标只需外延性。
-/
namespace YesMetaZFC.SetTheory.InnerModel.Relative
open Definitional.Project Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

theorem lr_truth_decode_l (hM : M.Models ZF) {ω B : M.Domain}
    (space : Baire_d (kp_pair_l (ZF.modelsKP hM)) ω B)
    {n} {φ : Formula 1 n} (hc : φ.FreeClosed)
    {b : (lr_model_l hM).Domain} (eq : b.val = B) {x : Fin n → (lr_model_l hM).Domain}
    (truth : Sr_truth_d b φ x) : Dr_truth_d B φ (fun i => (x i).val) := by
  let L := lr_model_l hM
  have inj : Function.Injective (Subtype.val : L.Domain → M.Domain) := fun _ _ h => Subtype.ext h
  have full (a : L.Domain) (y : M.Domain) : M.mem y a.val ↔ ∃ z : L.Domain, L.mem z a ∧ z.val = y :=
    ⟨fun h => ⟨⟨y,lr_transitive_l hM a.property h⟩,h,rfl⟩,fun ⟨_,h,e⟩ => e ▸ h⟩
  obtain ⟨S,tc⟩ := ZF.tc_exists_l (kp_pair_l (ZF.modelsKP hM)) hM B
  have seed : Lr_seed_d hM ω B S := ⟨space,tc⟩
  obtain ⟨params,Q,sub,sat⟩ := truth
  refine ⟨fun i => eq ▸ params i,S,tc,Q.val,(lr_iff_l hM seed Q.val).mp Q.property,?_,
    (st_image_l (M := L) (N := M) Subtype.val inj full Q φ hc x).mp sat⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := (full b y).mp (eq.symm ▸ hy)
  exact sub z hz

theorem Dr_truth_d.formula_image_l (hM : M.Models KP) (hN : Extensional N)
    (e : M.Domain → N.Domain) (inj : Function.Injective e)
    (full : ∀ a y, N.mem y (e a) ↔ ∃ z, M.mem z a ∧ e z = y)
    {D B : M.Domain} (trans : M.TransitiveSet D)
    (reals : ∀ f, M.mem f B → Fn0_d D D f) (ne : ∃ f, M.mem f B)
    {n} {φ : Formula 1 n} (hc : φ.FreeClosed) {x : Fin n → M.Domain} (truth : Dr_truth_d B φ x) :
    Formula.satisfies (⟨Fin.cases (e B) (fun i => e (x i)),fun _ => e B⟩ : Env N (n+1))
      (dr_m φ .newest (fun i => .bound i.succ)) := by
  let ρ : Env M (n+1) := ⟨Fin.cases B x,fun _ => B⟩
  let η := image_env_l e ρ
  obtain ⟨params,S,tc,Q,⟨α,W,layer,qW⟩,sub,sat⟩ := truth
  have tc' := real_tc_image_l hM hN e inj full trans reals ne tc
  have la : Formula.satisfies ((η.push (e S)).push (e Q)) (la_m (.bound 1) .newest) := by
    simp only [la_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,ja_value_sat_l,
      Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    refine ⟨e α,e W,?_,ja_value_image_l e inj full layer.2,(image_member_l e inj full).mpr qW⟩
    have old := (KP.ord0_sat_l hM ((((ρ.push S).push Q).push α).push W) (.bound 1)).mpr layer.1
    have moved := (delta0_image_l e inj full (KP.ord0_delta_l (.bound 1)) _).mp old
    simpa only [image_env_push_l] using! moved
  have env : η = (⟨Fin.cases (e B) (fun i => e (x i)),fun _ => e B⟩ : Env N (n+1)) := by
    rw [Env.mk.injEq]
    exact ⟨funext (Fin.cases rfl (fun _ => rfl)),rfl⟩
  rw [← env]
  simp only [dr_m,Formula.satisfies_conj_iff,st_params_sat_l,Formula.satisfies_exists_iff,
    tc_sat_l,Formula.satisfies_subset_iff,st_sat_l φ hc,Definitional.Term.eval_weaken]
  refine ⟨fun i => (image_member_l e inj full).mpr (params i),e S,tc',e Q,la,?_,
    (st_image_l e inj full Q φ hc x).mp sat⟩
  intro y hy
  obtain ⟨z,hz,rfl⟩ := (full B y).mp hy
  exact (image_member_l e inj full).mpr (sub z hz)

end YesMetaZFC.SetTheory.InnerModel.Relative
