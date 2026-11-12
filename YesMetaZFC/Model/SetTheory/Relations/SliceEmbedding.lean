import YesMetaZFC.Model.SetTheory.Embedding.Relative

/-! # 原关系切片之间的完整公式传输

先在两侧原结构内部相对化，再沿同一个完整初等图传输。参数属于各自
原切片，量词仍遍及整个切片；不要求原载体在背景中传递或已经坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.slice_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x C})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x D})
    (image : Rd_entry_d C.val D.val j) {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) C nc) n)
    (σ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) D nd) n)
    (points : ∀ i, Rd_entry_d (ρ.bound i).val.val (σ.bound i).val.val j) :
    Formula.satisfies ρ φ ↔ Formula.satisfies σ φ := by
  let ε : Env (smdl_structure_l I (R := R) mx.2.1) (n+1) :=
    ⟨Fin.cases C (fun i => (ρ.bound i).val), fun _ => C⟩
  let θ : Env (smdl_structure_l I (R := S) my.2.1) (n+1) :=
    ⟨Fin.cases D (fun i => (σ.bound i).val), fun _ => D⟩
  have left := sc_relative_sat_l ct nc φ closed ρ ε .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have right := sc_relative_sat_l dt nd φ closed σ θ .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  exact left.symm.trans ((smap_source_l I hZF hω mx my map
    (lr_rel_m φ .newest (fun i => .bound i.succ))
    (lr_rel_closed_l φ closed _ _ rfl (fun _ => rfl)) ε θ (Fin.cases image points)).trans right)

/-- 各坐标的实际像自动留在目标反射层，随后传输同一个完整公式。 -/
theorem Smap_d.slice_image_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x C})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x D})
    (image : Rd_entry_d C.val D.val j) {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) C nc) n) :
    ∃ σ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) D nd) n,
      (∀ i, Rd_entry_d (ρ.bound i).val.val (σ.bound i).val.val j) ∧
      (Formula.satisfies ρ φ ↔ Formula.satisfies σ φ) := by
  have values i : ∃ y : (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) D nd).Domain,
      Rd_entry_d (ρ.bound i).val.val y.val.val j := by
    obtain ⟨y, hy, pair⟩ := map.1.1.2.2 (ρ.bound i).val.val (ρ.bound i).val.property
    exact ⟨⟨⟨y, hy⟩, (map.relation_l I hZF hω mx my pair image).mp (ρ.bound i).property⟩, pair⟩
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice values
  have inhabited := nd
  obtain ⟨a⟩ := inhabited
  let σ := (⟨v, fun _ => a⟩ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) D nd) n)
  exact ⟨σ, hv, map.slice_l hZF hω mx my C D ct dt nc nd image φ closed ρ σ hv⟩

/-- 参数在共同根中有同一原像时，两侧原切片保持完整相对公式。 -/
theorem smap_slice_peer_l {ω b B R x X S y Y T j k C₀ : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mx : Smdl_d I x X S) (my : Smdl_d I y Y T)
    (left : Smap_d I ω b x B X j) (right : Smap_d I ω b y B Y k)
    (C : (smdl_structure_l I (R := S) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := T) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := S) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := T) my.2.1).TransitiveSet D)
    (nc : Nonempty {a : (smdl_structure_l I (R := S) mx.2.1).Domain //
      (smdl_structure_l I (R := S) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := T) my.2.1).Domain //
      (smdl_structure_l I (R := T) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val j) (iD : Rd_entry_d C₀ D.val k)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l C nc) n) (σ : Env (rt_model_l D nd) n)
    (v : Fin n → M.Domain)
    (ij : ∀ i, Rd_entry_d (v i) (ρ.bound i).val.val j)
    (ik : ∀ i, Rd_entry_d (v i) (σ.bound i).val.val k) :
    Formula.satisfies ρ φ ↔ Formula.satisfies σ φ := by
  let α : Env (smdl_structure_l I (R := R) mb.2.1) (n+1) :=
    ⟨Fin.cases ⟨C₀, left.1.1.input_mem_of_pairMember iC⟩
      (fun i => ⟨v i, left.1.1.input_mem_of_pairMember (ij i)⟩),
      fun _ => ⟨C₀, left.1.1.input_mem_of_pairMember iC⟩⟩
  let β : Env (smdl_structure_l I (R := S) mx.2.1) (n+1) :=
    ⟨Fin.cases C (fun i => (ρ.bound i).val), fun _ => C⟩
  let γ : Env (smdl_structure_l I (R := T) my.2.1) (n+1) :=
    ⟨Fin.cases D (fun i => (σ.bound i).val), fun _ => D⟩
  let Φ := lr_rel_m φ .newest (fun i => .bound i.succ)
  have hc : Φ.FreeClosed := lr_rel_closed_l φ closed _ _ rfl (fun _ => rfl)
  have l := smap_source_l I hZF hω mb mx left Φ hc α β (Fin.cases iC ij)
  have r := smap_source_l I hZF hω mb my right Φ hc α γ (Fin.cases iD ik)
  exact (sc_relative_sat_l ct nc φ closed ρ β .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).symm.trans
    (l.symm.trans (r.trans
      (sc_relative_sat_l dt nd φ closed σ γ .newest (fun i => .bound i.succ) rfl (fun _ => rfl))))

/-- 原生模型中的数值参数由共同根的完整数字坐标识别，保持整个公式。 -/
theorem smap_numeric_model_peer_l
    {ω b B R x X S y Y T j k w₀ z₀ w₁ z₁ w₂ z₂ : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mx : Smdl_d I x X S) (my : Smdl_d I y Y T)
    (left : Smap_d I ω b x B X j) (right : Smap_d I ω b y B Y k)
    (eb : Rf_ext_d I B R) (ex : Rf_ext_d I X S) (ey : Rf_ext_d I Y T)
    (root : Rr_layer_d I ω B R w₀ z₀) (source : Rr_layer_d I ω X S w₁ z₁)
    (target : Rr_layer_d I ω Y T w₂ z₂)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := S) mx.2.1) n)
    (σ : Env (smdl_structure_l I (R := T) my.2.1) n)
    (values : ∀ i, ((ρ.bound i).val = w₁ ∧ (σ.bound i).val = w₂) ∨
      ∃ a, Rd_entry_d a (ρ.bound i).val z₁ ∧ Rd_entry_d a (σ.bound i).val z₂) :
    Formula.satisfies ρ φ ↔ Formula.satisfies σ φ := by
  have jl := root.omega_map_l I hZF hω mb mx left eb ex source
  have kr := root.omega_map_l I hZF hω mb my right eb ey target
  have points i : ∃ a, Rd_entry_d a (ρ.bound i).val j ∧ Rd_entry_d a (σ.bound i).val k := by
    rcases values i with ⟨h,h'⟩ | ⟨a,ha,ha'⟩
    · exact ⟨w₀,h.symm ▸ jl.1,h'.symm ▸ kr.1⟩
    · obtain ⟨v,_,hav⟩ := root.injection.1.2.2 a (source.injection.1.input_mem_of_pairMember ha)
      exact ⟨v,jl.2 a v _ hav ha,kr.2 a v _ hav ha'⟩
  obtain ⟨v,hv⟩ := Classical.axiomOfChoice points
  let α : Env (smdl_structure_l I (R := R) mb.2.1) n :=
    ⟨fun i => ⟨v i,left.1.1.input_mem_of_pairMember (hv i).1⟩,fun _ => ⟨w₀,root.member⟩⟩
  exact (smap_source_l I hZF hω mb mx left φ closed α ρ (fun i => (hv i).1)).symm.trans
    (smap_source_l I hZF hω mb my right φ closed α σ (fun i => (hv i).2))

/-- 两个原切片中的数值参数由同一完整数字坐标识别，整个公式经共同根传输。 -/
theorem smap_numeric_slice_peer_l
    {ω b B R x X S y Y T j k C₀ w₀ z₀ w₁ z₁ w₂ z₂ : M.Domain}
    (hω : M.IsOmega ω) (mb : Smdl_d I b B R) (mx : Smdl_d I x X S) (my : Smdl_d I y Y T)
    (left : Smap_d I ω b x B X j) (right : Smap_d I ω b y B Y k)
    (eb : Rf_ext_d I B R) (ex : Rf_ext_d I X S) (ey : Rf_ext_d I Y T)
    (root : Rr_layer_d I ω B R w₀ z₀) (source : Rr_layer_d I ω X S w₁ z₁)
    (target : Rr_layer_d I ω Y T w₂ z₂)
    (C : (smdl_structure_l I (R := S) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := T) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := S) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := T) my.2.1).TransitiveSet D)
    (nc : Nonempty {a : (smdl_structure_l I (R := S) mx.2.1).Domain //
      (smdl_structure_l I (R := S) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := T) my.2.1).Domain //
      (smdl_structure_l I (R := T) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val j) (iD : Rd_entry_d C₀ D.val k)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l C nc) n) (σ : Env (rt_model_l D nd) n)
    (values : ∀ i, ((ρ.bound i).val.val = w₁ ∧ (σ.bound i).val.val = w₂) ∨
      ∃ a, Rd_entry_d a (ρ.bound i).val.val z₁ ∧ Rd_entry_d a (σ.bound i).val.val z₂) :
    Formula.satisfies ρ φ ↔ Formula.satisfies σ φ := by
  have jl := root.omega_map_l I hZF hω mb mx left eb ex source
  have kr := root.omega_map_l I hZF hω mb my right eb ey target
  have points i : ∃ a, Rd_entry_d a (ρ.bound i).val.val j ∧ Rd_entry_d a (σ.bound i).val.val k := by
    rcases values i with ⟨h, h'⟩ | ⟨a, ha, ha'⟩
    · exact ⟨w₀, h.symm ▸ jl.1, h'.symm ▸ kr.1⟩
    · obtain ⟨v, _, hav⟩ := root.injection.1.2.2 a (source.injection.1.input_mem_of_pairMember ha)
      exact ⟨v, jl.2 a v _ hav ha, kr.2 a v _ hav ha'⟩
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice points
  exact smap_slice_peer_l hZF hω mb mx my left right C D ct dt nc nd iC iD φ closed ρ σ v
    (fun i => (hv i).1) (fun i => (hv i).2)

end YesMetaZFC.SetTheory.Internal
