import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded
import YesMetaZFC.Model.SetTheory.Internal.RelationLayer

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
  let θ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  have left := sc_relative_sat_l ct nc φ hc ρ (θ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have right := sc_relative_sat_l dt nd φ hc η (θ.push D) .newest (fun i => .bound i.succ) rfl same
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

/-- 两个完整低层实现之间的实际图，由同一原关系边唯一确定。 -/
theorem Smap_d.layer_map_l {ω b B R u U S π C V H K f g : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mu : Smdl_d I u U S)
    (hj : Smap_d I ω b u B U π) (left : Rr_layer_d I C B R H f) (right : Rr_layer_d I V U S K g)
    (hHK : Rd_entry_d H K π) : ∃ t, M.IsSetInjectionFromTo I t C V ∧ ∀ x y,
      Rd_entry_d x y t ↔ M.mem x C ∧ ∃ a b, Rd_entry_d x a f ∧ Rd_entry_d a b π ∧ Rd_entry_d y b g := by
  let ρ : Env M 3 := ⟨Fin.cases π (Fin.cases g (fun _ => f)), fun _ => C⟩
  let φ : BinarySchema 3 := { body := .existsE (.existsE
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 6))
      (.conj (rd_entry0_m (.bound 1) .newest (.bound 4)) (rd_entry0_m (.bound 2) .newest (.bound 5))))) }
  have read x y : φ.denote ρ x y ↔ ∃ a b, Rd_entry_d x a f ∧ Rd_entry_d a b π ∧ Rd_entry_d y b g := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  have unique x y z (hy : φ.denote ρ x y) (hz : φ.denote ρ x z) : y = z := by
    obtain ⟨a, b, ha, hab, hb⟩ := (read x y).mp hy
    obtain ⟨a', b', ha', hab', hb'⟩ := (read x z).mp hz
    have ea := left.injection.1.1.2 x a a' ha ha'
    have eb := hj.1.1.1.2 a b b' hab (ea.symm ▸ hab')
    exact right.injection.2 y z b hb (eb.symm ▸ hb')
  obtain ⟨t, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := V) (by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := left.injection.1.2.2 x hx
    obtain ⟨b, _, hab⟩ := hj.1.1.2.2 a ha
    have hb := (hj.relation_l I hZF hω mb mu hab hHK).mp ((left.image a).mpr ⟨x, hx, hxa⟩)
    obtain ⟨y, _, hyb⟩ := (right.image b).mp hb
    exact ⟨y, (read x y).mpr ⟨a, b, hxa, hab, hyb⟩⟩)
    (fun x _ y z => unique x y z) (fun x y _ hy =>
      ((read x y).mp hy).elim fun a ha => ha.elim fun b hb => right.injection.1.input_mem_of_pairMember hb.2.2)
  refine ⟨t, ⟨fn, ?_⟩, fun x y => (spec x y).trans (and_congr Iff.rfl (read x y))⟩
  intro x y z hx hy
  obtain ⟨a, b, ha, hab, hb⟩ := (read x z).mp ((spec x z).mp hx).2
  obtain ⟨a', b', ha', hab', hb'⟩ := (read y z).mp ((spec y z).mp hy).2
  have eb := right.injection.1.1.2 z b b' hb hb'
  have ea := hj.1.2 a a' b hab (eb.symm ▸ hab')
  exact left.injection.2 x y a ha (ea.symm ▸ ha')

/-- 原关系边把完整低层记录传到下一实际低层；两侧高模型都无需传递。 -/
theorem Smap_d.relative_image_l {ω b B R u U S π C V H K f g : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mu : Smdl_d I u U S)
    (hj : Smap_d I ω b u B U π) (left : Rr_layer_d I C B R H f) (right : Rr_layer_d I V U S K g)
    (nc : Nonempty {x // M.mem x C}) (nv : Nonempty {x // M.mem x V}) (hHK : Rd_entry_d H K π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) :
    ∃ η : Env (rt_model_l V nv) n,
      (∀ i, ∃ x y, Rd_entry_d (ρ.bound i).val x f ∧ Rd_entry_d x y π ∧ Rd_entry_d (η.bound i).val y g) ∧
      (Formula.satisfies ρ φ ↔ Formula.satisfies η φ) := by
  have values (i : Fin n) : ∃ t : (smdl_structure_l I (R := R) mb.2.1).Domain ×
      (smdl_structure_l I (R := S) mu.2.1).Domain × (rt_model_l V nv).Domain,
      Rd_entry_d (ρ.bound i).val t.1.val f ∧ Rd_entry_d t.1.val t.2.1.val π ∧ Rd_entry_d t.2.2.val t.2.1.val g := by
    obtain ⟨x, hx, hix⟩ := left.injection.1.2.2 (ρ.bound i).val (ρ.bound i).property
    obtain ⟨y, hy, hxy⟩ := hj.1.1.2.2 x hx
    have inK : Rd_entry_d y K S := (hj.relation_l I hZF hω mb mu hxy hHK).mp
      ((left.image x).mpr ⟨(ρ.bound i).val, (ρ.bound i).property, hix⟩)
    obtain ⟨z, hz, hzy⟩ := (right.image y).mp inK
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩), hix, hxy, hzy⟩
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice values
  have inhabited := nv
  obtain ⟨z⟩ := inhabited
  let η : Env (rt_model_l V nv) n := ⟨fun i => (v i).2.2, fun _ => z⟩
  let σ : Env (smdl_structure_l I (R := R) mb.2.1) n := ⟨fun i => (v i).1, fun _ => ⟨H, left.member⟩⟩
  let τ : Env (smdl_structure_l I (R := S) mu.2.1) n := ⟨fun i => (v i).2.1, fun _ => ⟨K, right.member⟩⟩
  have old := left.relative_l I nc φ hc ρ (σ.push ⟨H, left.member⟩) .newest
    (fun i => .bound i.succ) rfl (fun i => (hv i).1)
  have new := right.relative_l I nv φ hc η (τ.push ⟨K, right.member⟩) .newest
    (fun i => .bound i.succ) rfl (fun i => (hv i).2.2)
  have moved := smap_source_l I hZF hω mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ hc _ _ rfl (fun _ => rfl)) (σ.push ⟨H, left.member⟩) (τ.push ⟨K, right.member⟩)
    (Fin.cases hHK (fun i => (hv i).2.1))
  exact ⟨η, fun i => ⟨(v i).1.val, (v i).2.1.val, hv i⟩, old.trans (moved.trans new.symm)⟩

theorem Smap_d.reflected_l {ω b B R u U S π C V : M.Domain}
    (hω : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C}) (hCV : Rd_entry_d C V π)
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (reflect : Lr_reflect_d φ V)
    (ρ : Env (rt_model_l C nc) n) (η : Env M n)
    (images : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i) π) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  let σ : Env M n := ⟨fun i => (ρ.bound i).val, fun i => (ρ.free i).val⟩
  have small := sc_relative_sat_l ct nc φ hc ρ (σ.push C) .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have tr := smap_delta_l I hZF hω bt ut mb mu hj (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ hc _ _ rfl (fun _ => rfl)) (lr_rel_delta_l ..)
    (σ.push C) (η.push V) (Fin.cases hCV images)
  exact small.symm.trans (tr.trans (reflect η (fun i =>
    (hj.member_l I hZF hω mb mu (images i) hCV).mp (ρ.bound i).property)).symm)

end YesMetaZFC.SetTheory.Internal
