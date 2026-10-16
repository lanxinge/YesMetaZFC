import YesMetaZFC.Model.SetTheory.Internal.RelationUniformCode
import YesMetaZFC.Model.SetTheory.Internal.SourceCollectionBasis

/-! # 小定义域统一化进入原始关系模型

把实际源的“小性守卫 ⇒ 收集蕴含”编成一个内部程序，再传输其全称闭包。
目标参数不需旧原像，程序码不需外部标准；所得见证仍是目标内部的函数对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem sc_collection_raw_l {ω c d X R Y S q K F n r i j g : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (hn : Smdl_d I d Y S) (ext : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X Y q)
    (source : Sc_collection_d I ω X R) (hK : M.IsFunctionSpace I K ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K)
    (D μ e : (smdl_structure_l I (R := S) hn.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases D (fun _ => e)), fun _ => D⟩ : Env (smdl_structure_l I (R := S) hn.2.1) 3)
      (sc_index_m .newest (.bound 1) (.bound 2)))
    (total : ∀ x : (smdl_structure_l I (R := S) hn.2.1).Domain, M.PairMember I x.val D.val S →
      ∃ y : (smdl_structure_l I (R := S) hn.2.1).Domain, Sbin_d I Y S K F n r i j g x.val y.val) :
    ∃ B C : (smdl_structure_l I (R := S) hn.2.1).Domain, Fn0_d D C B ∧
      ∀ x y : (smdl_structure_l I (R := S) hn.2.1).Domain,
        Rd_entry_d x y B → Sbin_d I Y S K F n r i j g x.val y.val := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨t, ht, htω⟩ := hω.1.2 s hs
  obtain ⟨u, hu, huω⟩ := hω.1.2 t htω
  obtain ⟨σ, hσ, hσω⟩ := hω.1.2 u huω
  have st : M.MemberSubset s t := fun x hx => (ht x).mpr (Or.inl hx)
  have tu : M.MemberSubset t u := fun x hx => (hu x).mpr (Or.inl hx)
  have uσ : M.MemberSubset u σ := fun x hx => (hσ x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun eq => ir i (eq ▸ his)
  obtain ⟨n₁, F₁, r₁, h₁, uniform⟩ := sfm_uniform_raw_l I hZF hω hF hr hσω
    (uσ i (tu i (st i his))) (uσ j (tu j (st j hjs))) (uσ s (tu s ht.predecessor_mem))
    (uσ t hu.predecessor_mem) hσ.predecessor_mem hij hsi (fun eq => ir i (eq ▸ st i his))
    (fun eq => ir j (eq ▸ st j hjs)) (fun eq => ir t (eq ▸ ht.predecessor_mem))
    (fun eq => ir s (eq ▸ tu s ht.predecessor_mem)) (fun eq => ir t (eq ▸ hu.predecessor_mem)) hb (fun h => ir t (st t h))
  obtain ⟨n₂, F₂, r₂, h₂, antecedent⟩ := sfm_total_raw_l I hZF hω h₁.program (h₁.span r hr) hi hj hs hsi
  obtain ⟨m, G, k, build, implication⟩ := sfm_imp_l I hZF hω h₂.program h₂.root (h₂.span r₁ h₁.root)
  have initial Z U E f x y : Sbin_d I Z U E F₁ n₁ r i j f x y ↔ Sbin_d I Z U E F n r i j f x y :=
    exists_congr fun v => exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
      (h₁.sat_l I hZF hF hr Z U E w).symm
  have read Z U E b f (model : Smdl_d I b Z U) (A : (smdl_structure_l I (R := U) model.2.1).Domain)
      (ext : Extensional (smdl_structure_l I (R := U) model.2.1))
      (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E) (hA : M.PairMember I s A.val f) :
      Ssat_d I Z U E G m k f ↔
        ((∀ x : (smdl_structure_l I (R := U) model.2.1).Domain, M.PairMember I x.val A.val U →
          ∃ y : (smdl_structure_l I (R := U) model.2.1).Domain, Sbin_d I Z U E F n r i j f x.val y.val) →
        ∃ B C : (smdl_structure_l I (R := U) model.2.1).Domain, Fn0_d A C B ∧
          ∀ x y : (smdl_structure_l I (R := U) model.2.1).Domain, Rd_entry_d x y B → Sbin_d I Z U E F n r i j f x.val y.val) := by
    rw [implication Z U E f hf, antecedent Z U E b f model A hE hf hA,
      ← h₂.sat_l I hZF h₁.program h₁.root Z U E f, uniform Z U E b f model A ext hE hf hA]
    exact imp_congr (forall_congr' fun x => imp_congr_right fun _ => exists_congr fun y => initial Z U E f x.val y.val) Iff.rfl
  obtain ⟨τ, hτ, hτω⟩ := hω.1.2 σ hσω
  -- 编号序数和单射图另占两个支撑外槽位，小性守卫与原收集蕴含一起传输。
  obtain ⟨ν, hν, hνω⟩ := hω.1.2 τ hτω
  let v : Fin 3 → M.Domain := Fin.cases σ (Fin.cases s (fun _ => τ))
  have vs : ∀ a, M.mem (v a) ν := Fin.cases ((hν σ).mpr (Or.inl hτ.predecessor_mem))
    (Fin.cases ((hν s).mpr (Or.inl ((hτ s).mpr (Or.inl (uσ s (tu s ht.predecessor_mem)))))) (fun _ => hν.predecessor_mem))
  let φ : Formula 1 3 := sc_index_m .newest (.bound 1) (.bound 2)
  obtain ⟨n₃, F₃, r₃, h₃, index⟩ := sfm_template_l I hZF hω build.program φ
    (by simp -implicitDefEqProofs [φ]) v hνω vs
  obtain ⟨n₄, F₄, r₄, h₄, guarded⟩ := sfm_imp_l I hZF hω h₃.program h₃.root (h₃.span k build.root)
  have read' Z U E b f (model : Smdl_d I b Z U) (A μ e : (smdl_structure_l I (R := U) model.2.1).Domain)
      (ext : Extensional (smdl_structure_l I (R := U) model.2.1)) (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E)
      (hA : M.PairMember I s A.val f) (hμ : M.PairMember I σ μ.val f) (he : M.PairMember I τ e.val f) :
      Ssat_d I Z U E F₄ n₄ r₄ f ↔
        (Formula.satisfies (⟨Fin.cases μ (Fin.cases A (fun _ => e)), fun _ => A⟩ : Env (smdl_structure_l I (R := U) model.2.1) 3) φ →
        (∀ x : (smdl_structure_l I (R := U) model.2.1).Domain, M.PairMember I x.val A.val U →
          ∃ y : (smdl_structure_l I (R := U) model.2.1).Domain, Sbin_d I Z U E F n r i j f x.val y.val) →
        ∃ B C : (smdl_structure_l I (R := U) model.2.1).Domain, Fn0_d A C B ∧
          ∀ x y : (smdl_structure_l I (R := U) model.2.1).Domain, Rd_entry_d x y B → Sbin_d I Z U E F n r i j f x.val y.val) := by
    rw [guarded Z U E f hf, index Z U model.2.1 E hE f hf
      ⟨Fin.cases μ (Fin.cases A (fun _ => e)), fun _ => A⟩ (Fin.cases hμ (Fin.cases hA (fun _ => he))),
      ← h₃.sat_l I hZF build.program build.root Z U E f, read Z U E b f model A ext hE hf hA]
    rfl
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  have ex := smem_ext_l I hm.1 hm.2 hX hZF.1
  have valid f (hf : M.mem f E) : Ssat_d I X R E F₄ n₄ r₄ f := by
    -- 这里调用源中已实现的收集；目标的统一化不是额外假设。
    obtain ⟨A, hA, hsA⟩ := ((hE f).mp hf).2.2 s hs
    obtain ⟨μ, hμ, hσμ⟩ := ((hE f).mp hf).2.2 σ hσω
    obtain ⟨e, he, hτe⟩ := ((hE f).mp hf).2.2 τ hτω
    apply (read' X R E c f hm.1 ⟨A, hA⟩ ⟨μ, hμ⟩ ⟨e, he⟩ ex hE hf hsA hσμ hτe).mpr
    intro idx total
    have idx' := (smem_delta_image_l I hm hX (sc_index_delta_l ..) _).mp idx
    have idx : Sc_index_d μ A e := (sc_index_sat_l (ZF.modelsKP hZF) _ .newest (.bound 1) (.bound 2)).mp idx'
    obtain ⟨B, C, hB, hC, fn, truth⟩ := source A hA ⟨μ, e, hμ, he, idx⟩ E F n r i j f A hE hF hr hi hj hij hf hA
      (fun _ h => h) (fun x hx => by
        obtain ⟨y, hy⟩ := total ⟨x, hX A hA x hx⟩ ((hm.2 x A).mpr ⟨hX A hA x hx, hA, hx⟩)
        exact ⟨y.val, y.property, hy⟩)
    let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 3 :=
      ⟨Fin.cases ⟨A, hA⟩ (Fin.cases ⟨C, hC⟩ (fun _ => ⟨B, hB⟩)), fun _ => ⟨A, hA⟩⟩
    have fn' := (fn0_sat_l ex ρ .newest (.bound 1) (.bound 2)).mp
      ((smem_delta_image_l I hm hX (fn0_delta_l ..) ρ).mpr ((fn0_sat_l hZF.1 ..).mpr fn))
    refine ⟨⟨B, hB⟩, ⟨C, hC⟩, fn', fun x y hxy => ?_⟩
    let η : Env (smdl_structure_l I (R := R) hm.1.2.1) 3 := ⟨Fin.cases x (Fin.cases y (fun _ => ⟨B, hB⟩)), fun _ => x⟩
    exact truth x.val y.val ((rd_entry0_sat_l hZF.1 ..).mp
      ((smem_delta_image_l I hm hX (rd_entry0_delta_l ..) η).mp ((rd_entry0_sat_l ex η .newest (.bound 1) (.bound 2)).mpr hxy)))
  -- 更新全在原支撑之外，因此保留任意内部原公式的真值。
  obtain ⟨g₀, u₀, hg₀⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs D.property
  obtain ⟨g₁, u₁, hg₁⟩ := senv_update_exists_l I hZF hg₀ hσω μ.property
  obtain ⟨g₂, u₂, hg₂⟩ := senv_update_exists_l I hZF hg₁ hτω e.property
  have ns : ¬ M.mem σ s := fun h => ir σ (uσ σ (tu σ (st σ h)))
  have nt : ¬ M.mem τ s := fun h => ir τ ((hτ τ).mpr (Or.inl (uσ τ (tu τ (st τ h)))))
  have agree : Senv_agree_d I s g g₂ := fun a x ha =>
    (u₀.agree_l I (ir s) a x ha).trans ((u₁.agree_l I ns a x ha).trans (u₂.agree_l I nt a x ha))
  have aslot : M.PairMember I s D.val g₂ := (u₂.2 s D.val).mpr (Or.inr ⟨fun eq => ir τ (eq ▸ (hτ s).mpr (Or.inl (uσ s (tu s ht.predecessor_mem)))),
    (u₁.2 s D.val).mpr (Or.inr ⟨fun eq => ir σ (eq ▸ uσ s (tu s ht.predecessor_mem)), (u₀.2 s D.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
  have mslot : M.PairMember I σ μ.val g₂ := (u₂.2 σ μ.val).mpr
    (Or.inr ⟨fun eq => ir τ (eq ▸ hτ.predecessor_mem), (u₁.2 σ μ.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
  have eslot : M.PairMember I τ e.val g₂ := (u₂.2 τ e.val).mpr (Or.inl ⟨rfl, rfl⟩)
  have tr (x y : (smdl_structure_l I (R := S) hn.2.1).Domain) :=
    sbin_agree_l I hZF hF hb hr hi hj hK hg ((hK g₂).mpr hg₂) agree x.property y.property (R := S)
  obtain ⟨B, C, fn, truth⟩ := (read' Y S K d g₂ hn D μ e ext hK ((hK g₂).mpr hg₂) aslot mslot eslot).mp
    ((hq.valid_l I hZF hω hm.1 hn h₄.program h₄.root hE hK).mp valid g₂ ((hK g₂).mpr hg₂)) small
    (fun x hx => (total x hx).imp fun y hy => (tr x y).mp hy)
  exact ⟨B, C, fn, fun x y hxy => (tr x y).mpr (truth x y hxy)⟩

/-- 大集合上逐点存在已足够：追加成员守卫，在其余坐标仍产生源内的全定义代表。 -/
theorem sc_collection_on_raw_l {ω c d X R Y S q K F n r i j g : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (hn : Smdl_d I d Y S) (ext : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X Y q)
    (source : Sc_collection_d I ω X R) (hK : M.IsFunctionSpace I K ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K)
    (D A μ e : (smdl_structure_l I (R := S) hn.2.1).Domain)
    (small : Formula.satisfies (⟨Fin.cases μ (Fin.cases D (fun _ => e)), fun _ => D⟩ : Env (smdl_structure_l I (R := S) hn.2.1) 3)
      (sc_index_m .newest (.bound 1) (.bound 2)))
    (total : ∀ x : (smdl_structure_l I (R := S) hn.2.1).Domain, M.PairMember I x.val D.val S → M.PairMember I x.val A.val S →
      ∃ y : (smdl_structure_l I (R := S) hn.2.1).Domain, Sbin_d I Y S K F n r i j g x.val y.val) :
    ∃ B C : (smdl_structure_l I (R := S) hn.2.1).Domain, Fn0_d D C B ∧
      ∀ x y : (smdl_structure_l I (R := S) hn.2.1).Domain, Rd_entry_d x y B → M.PairMember I x.val A.val S →
        Sbin_d I Y S K F n r i j g x.val y.val := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun eq => ir i (eq ▸ his)
  have hsj : s ≠ j := fun eq => ir j (eq ▸ hjs)
  obtain ⟨m, G, build, atom⟩ := sfm_rel_l I hZF hω hF hi hs
  obtain ⟨l, H, k, step, implication⟩ := sfm_imp_l I hZF hω build.program build.root (build.span r hr)
  obtain ⟨g', update, hg'⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs A.property
  have hgK := (hK g').mpr hg'
  have point (x y : (smdl_structure_l I (R := S) hn.2.1).Domain) :
      Sbin_d I Y S K H l k i j g' x.val y.val ↔
        (M.PairMember I x.val A.val S → Sbin_d I Y S K F n r i j g x.val y.val) := by
    obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF hg' hi x.property
    obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF hvf hj y.property
    have old : Sbin_d I Y S K F n r i j g x.val y.val ↔ Ssat_d I Y S K F n r w :=
      (sbin_agree_l I hZF hF hb hr hi hj hK hg hgK (update.agree_l I (ir s)) x.property y.property).trans
        (sbin_value_l I hZF.1 hv hw)
    apply (sbin_value_l I hZF.1 hv hw).trans
    rw [implication Y S K w ((hK w).mpr hwf), atom Y S K w x.val A.val hK ((hK w).mpr hwf)
      ((hw.2 i x.val).mpr (Or.inr ⟨hij, (hv.2 i x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
      ((hw.2 s A.val).mpr (Or.inr ⟨hsj, (hv.2 s A.val).mpr (Or.inr ⟨hsi, (update.2 s A.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)),
      ← build.sat_l I hZF hF hr Y S K w]
    exact imp_congr Iff.rfl old.symm
  obtain ⟨B, C, fn, truth⟩ := sc_collection_raw_l I hZF hω hX hm hn ext hq source hK step.program step.root hi hj hij hgK
    D μ e small (fun x hx => by
      classical
      by_cases hA : M.PairMember I x.val A.val S
      · obtain ⟨y, hy⟩ := total x hx hA
        exact ⟨y, (point x y).mpr (fun _ => hy)⟩
      · exact ⟨D, (point x D).mpr (fun h => (hA h).elim)⟩)
  exact ⟨B, C, fn, fun x y hxy => (point x y).mp (truth x y hxy)⟩

end YesMetaZFC.SetTheory.Internal
