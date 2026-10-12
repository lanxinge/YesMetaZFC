import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded

/-! # 拥有集合中的原公式沿外层初等图回拉

先对原公式作全量词有界化，再由外层图传输。反射只用于给定有限原公式，
不把外部逐公式保持当作全内部初等性的替代。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定实际固定条目时，同一个原公式沿其所属集合搬运。 -/
theorem Smap_d.fixed_relative_l {ω b B R u U S π C V : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hCV : Rd_entry_d C V π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env M n)
    (fixed : ∀ i, Rd_entry_d (ρ.bound i) (ρ.bound i) π) :
    Formula.satisfies (ρ.push C) (lr_rel_m φ .newest (fun i => .bound i.succ)) ↔
      Formula.satisfies (ρ.push V) (lr_rel_m φ .newest (fun i => .bound i.succ)) := by
  exact smap_delta_l I hZF hω bt ut mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l _ hc _ _ rfl (fun _ => rfl)) (lr_rel_delta_l ..) (ρ.push C) (ρ.push V) (Fin.cases hCV fixed)

/-- 同一原层的两个初等像，对两条图实际固定的参数保持同一个原公式。 -/
theorem smap_fixed_peer_l {ω b B R x X S y Y T π σ C₀ C D : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smem_d I b B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω b x B X π) (k : Smap_d I ω b y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) (η : Env (rt_model_l D nd) n)
    (same : ∀ i, (ρ.bound i).val = (η.bound i).val)
    (fixed : ∀ i, Rd_entry_d (ρ.bound i).val (ρ.bound i).val π)
    (fixed' : ∀ i, Rd_entry_d (ρ.bound i).val (ρ.bound i).val σ) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have neC := nc
  have neD := nd
  obtain ⟨a⟩ := neC
  obtain ⟨d⟩ := neD
  obtain ⟨c, U, code⟩ := smdl_membership_l I hZF ⟨a.val, a.property⟩
  obtain ⟨e, V, code'⟩ := smdl_membership_l I hZF ⟨d.val, d.property⟩
  let θ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  have left := sc_relative_sat_l I code ct nc φ hc ρ (θ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have right := sc_relative_sat_l I code' dt nd φ hc η (θ.push D) .newest (fun i => .bound i.succ) rfl same
  exact left.symm.trans ((j.fixed_relative_l hZF hω bt xt mb mx iC φ hc θ fixed).symm.trans
    ((k.fixed_relative_l hZF hω bt yt mb my iD φ hc θ fixed').trans right))

/-- 内部自然数及 ω 无须另交固定性证明。 -/
theorem smap_numeric_peer_l {ω b B R x X S y Y T π σ C₀ C D : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smem_d I b B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω b x B X π) (k : Smap_d I ω b y B Y σ) (hw : M.mem ω B)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) (η : Env (rt_model_l D nd) n)
    (same : ∀ i, (ρ.bound i).val = (η.bound i).val) (low : ∀ i, (ρ.bound i).val = ω ∨ M.mem (ρ.bound i).val ω) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have jw := j.omega_l I hZF hω bt xt mb mx hw
  have kw := k.omega_l I hZF hω bt yt mb my hw
  have jn := j.natural_l hZF hω bt xt mb mx hw
  have kn := k.natural_l hZF hω bt yt mb my hw
  exact smap_fixed_peer_l hZF hω bt xt yt mb mx my j k iC iD ct dt nc nd φ hc ρ η same
    (fun i => (low i).elim (fun eq => eq.symm ▸ jw) (jn (ρ.bound i).val))
    (fun i => (low i).elim (fun eq => eq.symm ▸ kw) (kn (ρ.bound i).val))

/-- 有限个实际图条目递归组成目标赋值；整个原公式在两个所属集合之间搬运。 -/
theorem Smap_d.relative_image_l {ω b B R u U S π C V : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ct : M.TransitiveSet C) (vt : M.TransitiveSet V)
    (nc : Nonempty {x // M.mem x C}) (nv : Nonempty {x // M.mem x V}) (hCV : Rd_entry_d C V π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) :
    ∃ η : Env (rt_model_l V nv) n, (∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val π) ∧
      (Formula.satisfies ρ φ ↔ Formula.satisfies η φ) := by
  have pick : ∀ {k} (p : Fin k → M.Domain), (∀ i, ∃ y, Rd_entry_d (p i) y π) →
      ∃ q : Fin k → M.Domain, ∀ i, Rd_entry_d (p i) (q i) π := by
    intro k
    induction k with
    | zero => exact fun _ _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ k ih =>
      intro p all
      obtain ⟨y, hy⟩ := all 0
      obtain ⟨q, hq⟩ := ih (fun i => p i.succ) (fun i => all i.succ)
      exact ⟨Fin.cases y q, Fin.cases hy hq⟩
  obtain ⟨q, images⟩ := pick (fun i => (ρ.bound i).val) (fun i =>
    (hj.1.1.2.2 (ρ.bound i).val (bt C (hj.1.1.input_mem_of_pairMember hCV) _ (ρ.bound i).property)).imp
      fun _ h => h.2)
  have members i := (hj.member_l I hZF hω mb mu (images i) hCV).mp (ρ.bound i).property
  have inhabitedC := nc
  have inhabitedV := nv
  obtain ⟨x⟩ := inhabitedC
  obtain ⟨y⟩ := inhabitedV
  let η : Env (rt_model_l V nv) n := ⟨fun i => ⟨q i, members i⟩, fun _ => y⟩
  let σ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  let τ : Env M n := ⟨fun i => (η.bound i).val, fun i => (η.free i).val⟩
  obtain ⟨c, Q, code⟩ := smdl_membership_l I hZF ⟨x.val, x.property⟩
  obtain ⟨v, T, code'⟩ := smdl_membership_l I hZF ⟨y.val, y.property⟩
  have left := sc_relative_sat_l I code ct nc φ hc ρ (σ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have right := sc_relative_sat_l I code' vt nv φ hc η (τ.push V) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have tr := smap_delta_l I hZF hω bt ut mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ hc _ _ rfl (fun _ => rfl)) (lr_rel_delta_l ..)
    (σ.push C) (τ.push V) (Fin.cases hCV images)
  exact ⟨η, images, left.symm.trans (tr.trans right)⟩

theorem Smap_d.reflected_l {ω b B R u U S π C V : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) (hCV : Rd_entry_d C V π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (reflect : Lr_reflect_d φ V)
    (ρ : Env (rt_model_l C nc) n) (η : Env M n)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have inhabited := nc
  obtain ⟨x⟩ := inhabited
  obtain ⟨c, Q, code⟩ := smdl_membership_l I hZF ⟨x.val, x.property⟩
  let σ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  have small := sc_relative_sat_l I code ct nc φ hc ρ (σ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have tr := smap_delta_l I hZF hω bt ut mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ hc _ _ rfl (fun _ => rfl)) (lr_rel_delta_l ..)
    (σ.push C) (η.push V) (Fin.cases hCV images)
  exact small.symm.trans (tr.trans (reflect η (fun i =>
    (hj.member_l I hZF hω mb mu (images i) hCV).mp (ρ.bound i).property)).symm)

end YesMetaZFC.SetTheory.Internal
