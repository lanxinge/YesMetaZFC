import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded
import YesMetaZFC.Model.SetTheory.Relations.Parity

/-! # 拥有集合中的原公式沿外层初等图回拉

先对原公式作全量词有界化，再由外层图传输。反射只用于给定有限原公式，
不把外部逐公式保持当作全内部初等性的替代。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两个完整低层经同一原关系根交换原公式；三个高模型均使用自己的关系。 -/
theorem smap_peer_l {ω b B R x X S y Y T π σ C₀ C D H K f g : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mx : Smdl_d I x X S) (my : Smdl_d I y Y T)
    (j : Smap_d I ω b x B X π) (k : Smap_d I ω b y B Y σ)
    (left : Rr_layer_d I C X S H f) (right : Rr_layer_d I D Y T K g)
    (iC : Rd_entry_d C₀ H π) (iD : Rd_entry_d C₀ K σ)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) (η : Env (rt_model_l D nd) n)
    (v a a' : Fin n → M.Domain) (ij : ∀ i, Rd_entry_d (v i) (a i) π) (ik : ∀ i, Rd_entry_d (v i) (a' i) σ)
    (ic : ∀ i, Rd_entry_d (ρ.bound i).val (a i) f) (id : ∀ i, Rd_entry_d (η.bound i).val (a' i) g) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  let α : Env (smdl_structure_l I (R := R) mb.2.1) (n+1) :=
    ⟨Fin.cases ⟨C₀, j.1.1.input_mem_of_pairMember iC⟩ (fun i => ⟨v i, j.1.1.input_mem_of_pairMember (ij i)⟩),
      fun _ => ⟨C₀, j.1.1.input_mem_of_pairMember iC⟩⟩
  let β : Env (smdl_structure_l I (R := S) mx.2.1) (n+1) :=
    ⟨Fin.cases ⟨H, left.member⟩ (fun i => ⟨a i, j.1.1.output_mem_of_pairMember (ij i)⟩), fun _ => ⟨H, left.member⟩⟩
  let γ : Env (smdl_structure_l I (R := T) my.2.1) (n+1) :=
    ⟨Fin.cases ⟨K, right.member⟩ (fun i => ⟨a' i, k.1.1.output_mem_of_pairMember (ik i)⟩), fun _ => ⟨K, right.member⟩⟩
  let Φ : Formula 1 (n+1) := lr_rel_m φ .newest (fun i => .bound i.succ)
  have closed : Φ.FreeClosed := lr_rel_closed_l _ hc _ _ rfl (fun _ => rfl)
  have jφ := smap_source_l I hZF hω mb mx j Φ closed α β (Fin.cases iC ij)
  have kφ := smap_source_l I hZF hω mb my k Φ closed α γ (Fin.cases iD ik)
  have l := left.relative_l I nc φ hc ρ β .newest (fun i => .bound i.succ) rfl ic
  have r := right.relative_l I nd φ hc η γ .newest (fun i => .bound i.succ) rfl id
  exact l.trans (jφ.symm.trans (kφ.trans r.symm))

/-- 全部背景内部自然数的原像由同一数字图给出，两侧程序使用相同数值。 -/
theorem smap_numeric_peer_l {ω b B R w z x X S y Y T π σ C₀ C D : M.Domain}
    (hω : M.IsOmega ω) (numbers : Rr_layer_d I ω B R w z) (ext : Rf_ext_d I B R)
    (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mb : Smdl_d I b B R) (mx : Smem_d I x X S) (my : Smem_d I y Y T)
    (j : Smap_d I ω b x B X π) (k : Smap_d I ω b y B Y σ)
    (iC : Rd_entry_d C₀ C π) (iD : Rd_entry_d C₀ D σ)
    (ct : M.TransitiveSet C) (dt : M.TransitiveSet D)
    (nc : Nonempty {a // M.mem a C}) (nd : Nonempty {a // M.mem a D})
    {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n) (η : Env (rt_model_l D nd) n)
    (same : ∀ i, (ρ.bound i).val = (η.bound i).val) (low : ∀ i, (ρ.bound i).val = ω ∨ M.mem (ρ.bound i).val ω) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  have jn := numbers.omega_image_mem_l I hZF hω ext mb mx xt j
  have kn := numbers.omega_image_mem_l I hZF hω ext mb my yt k
  have values i : ∃ a, Rd_entry_d a (ρ.bound i).val π ∧ Rd_entry_d a (η.bound i).val σ := by
    rcases low i with eq | hi
    · have eq' := (same i).symm.trans eq
      exact ⟨w, eq.symm ▸ jn.1, eq'.symm ▸ kn.1⟩
    · obtain ⟨a, _, hna⟩ := numbers.injection.1.2.2 (ρ.bound i).val hi
      exact ⟨a, jn.2 _ _ hna, (same i) ▸ kn.2 _ _ hna⟩
  obtain ⟨v, images⟩ := Classical.axiomOfChoice values
  obtain ⟨f, left, cf⟩ := rr_layer_mem_l I hZF mx xt (j.1.1.output_mem_of_pairMember iC) ct
  obtain ⟨g, right, dg⟩ := rr_layer_mem_l I hZF my yt (k.1.1.output_mem_of_pairMember iD) dt
  exact smap_peer_l hZF hω mb mx.1 my.1 j k left right iC iD nc nd φ hc ρ η v
    (fun i => (ρ.bound i).val) (fun i => (η.bound i).val)
    (fun i => (images i).1) (fun i => (images i).2)
    (fun i => (cf _ _).mpr ⟨(ρ.bound i).property, rfl⟩)
    (fun i => (dg _ _).mpr ⟨(η.bound i).property, rfl⟩)

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
