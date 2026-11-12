import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis

/-! # 小定义域统一化进入原始关系模型

把“小性、子集守卫 ⇒ 收集蕴含”编成一个内部程序，再双向传输其全称闭包。
目标参数不需旧原像，程序码不需外部标准；所得见证仍是目标内部的函数对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

/-- 小性、任意子集及统一函数的全称闭包沿实际初等图双向传输。 -/
theorem sc_collection_iff_l {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S)
    (ex : Extensional (smdl_structure_l I (R := R) hm.2.1))
    (ey : Extensional (smdl_structure_l I (R := S) hn.2.1)) (hq : Smap_d I ω c d X Y q) :
    Sc_collection_d I ω X R ↔ Sc_collection_d I ω Y S := by
  have move {c d X R Y S : M.Domain} (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S)
      (ex : Extensional (smdl_structure_l I (R := R) hm.2.1))
      (ext : Extensional (smdl_structure_l I (R := S) hn.2.1))
      (transfer : ∀ n F r E K : M.Domain, Sfm_d I ω n F → M.mem r n →
        M.IsFunctionSpace I E ω X → M.IsFunctionSpace I K ω Y →
        (∀ f, M.mem f E → Ssat_d I X R E F n r f) → ∀ g, M.mem g K → Ssat_d I Y S K F n r g)
      (source : Sc_collection_d I ω X R) : Sc_collection_d I ω Y S := by
    intro ny D μ e idx nz K F n r i j g A hK hF hr hi hj hij hg hA sub total
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
    obtain ⟨ν, hν, hνω⟩ := hω.1.2 τ hτω
    obtain ⟨δ, hδ, hδω⟩ := hω.1.2 ν hνω
    have στ : M.MemberSubset σ τ := fun x hx => (hτ x).mpr (Or.inl hx)
    have τν : M.MemberSubset τ ν := fun x hx => (hν x).mpr (Or.inl hx)
    have νδ : M.MemberSubset ν δ := fun x hx => (hδ x).mpr (Or.inl hx)
    have sσ := uσ s (tu s ht.predecessor_mem)
    have sτ := στ s sσ
    have sν := τν s sτ
    have σν := τν σ hτ.predecessor_mem
    let v : Fin 4 → M.Domain := Fin.cases σ (Fin.cases ν (Fin.cases τ (fun _ => s)))
    have vs : ∀ a, M.mem (v a) δ := Fin.cases (νδ σ σν)
      (Fin.cases hδ.predecessor_mem (Fin.cases (νδ τ hν.predecessor_mem) (fun _ => νδ s sν)))
    -- 编号约束作用于 D；待统一的任意子集 A 与 D 分别占用槽位。
    let φ : Formula 1 4 := .conj (sc_index_m .newest (.bound 1) (.bound 2)) (Formula.subset (.bound 3) (.bound 1))
    obtain ⟨n₃, F₃, r₃, h₃, index⟩ := sfm_template_l I hZF hω build.program φ
      (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) v hδω vs
    obtain ⟨n₄, F₄, r₄, h₄, guarded⟩ := sfm_imp_l I hZF hω h₃.program h₃.root (h₃.span k build.root)
    have read' Z U E b f (model : Smdl_d I b Z U) (A D μ e : (smdl_structure_l I (R := U) model.2.1).Domain)
        (en : Extensional (smdl_structure_l I (R := U) model.2.1)) (hE : M.IsFunctionSpace I E ω Z) (hf : M.mem f E)
        (hA : M.PairMember I s A.val f) (hμ : M.PairMember I σ μ.val f)
        (he : M.PairMember I τ e.val f) (hD : M.PairMember I ν D.val f) :
        Ssat_d I Z U E F₄ n₄ r₄ f ↔
          (Formula.satisfies (⟨Fin.cases μ (Fin.cases D (fun _ => e)), fun _ => D⟩ : Env (smdl_structure_l I (R := U) model.2.1) 3)
            (sc_index_m .newest (.bound 1) (.bound 2)) ∧ (smdl_structure_l I (R := U) model.2.1).MemberSubset A D) →
          (∀ x : (smdl_structure_l I (R := U) model.2.1).Domain, M.PairMember I x.val A.val U →
            ∃ y : (smdl_structure_l I (R := U) model.2.1).Domain, Sbin_d I Z U E F n r i j f x.val y.val) →
          ∃ B C : (smdl_structure_l I (R := U) model.2.1).Domain, Fn0_d A C B ∧
            ∀ x y : (smdl_structure_l I (R := U) model.2.1).Domain, Rd_entry_d x y B → Sbin_d I Z U E F n r i j f x.val y.val := by
      let ρ : Env (smdl_structure_l I (R := U) model.2.1) 4 :=
        ⟨Fin.cases μ (Fin.cases D (Fin.cases e (fun _ => A))), fun _ => A⟩
      rw [guarded Z U E f hf, index Z U model.2.1 E hE f hf ρ
        (Fin.cases hμ (Fin.cases hD (Fin.cases he (fun _ => hA)))),
        ← h₃.sat_l I hZF build.program build.root Z U E f, read Z U E b f model A en hE hf hA]
      rfl
    obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
    have valid f (hf : M.mem f E) : Ssat_d I X R E F₄ n₄ r₄ f := by
      obtain ⟨A, hA, hsA⟩ := ((hE f).mp hf).2.2 s hs
      obtain ⟨D, hD, hνD⟩ := ((hE f).mp hf).2.2 ν hνω
      obtain ⟨μ, hμ, hσμ⟩ := ((hE f).mp hf).2.2 σ hσω
      obtain ⟨e, he, hτe⟩ := ((hE f).mp hf).2.2 τ hτω
      apply (read' X R E c f hm ⟨A, hA⟩ ⟨D, hD⟩ ⟨μ, hμ⟩ ⟨e, he⟩ ex hE hf hsA hσμ hτe hνD).mpr
      intro guard total
      exact source hm.2.1 ⟨D, hD⟩ ⟨μ, hμ⟩ ⟨e, he⟩ guard.1 hm.2.1 E F n r i j f A hE hF hr hi hj hij hf hA
        (fun x hx ha => guard.2 ⟨x, hx⟩ ha)
        (fun x hx ha => (total ⟨x, hx⟩ ha).elim fun y hy => ⟨y.val, y.property, hy⟩)
    -- 四个新槽位均在原支撑外，原赋值在整个内部程序上的真值不变。
    obtain ⟨g₀, u₀, hg₀⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs hA
    obtain ⟨g₁, u₁, hg₁⟩ := senv_update_exists_l I hZF hg₀ hσω μ.property
    obtain ⟨g₂, u₂, hg₂⟩ := senv_update_exists_l I hZF hg₁ hτω e.property
    obtain ⟨g₃, u₃, hg₃⟩ := senv_update_exists_l I hZF hg₂ hνω D.property
    have ns : ¬ M.mem σ s := fun h => ir σ (uσ σ (tu σ (st σ h)))
    have nt : ¬ M.mem τ s := fun h => ir τ (στ τ (uσ τ (tu τ (st τ h))))
    have nv : ¬ M.mem ν s := fun h => ir ν (τν ν (στ ν (uσ ν (tu ν (st ν h)))))
    have agree : Senv_agree_d I s g g₃ := fun a x ha =>
      (u₀.agree_l I (ir s) a x ha).trans ((u₁.agree_l I ns a x ha).trans
        ((u₂.agree_l I nt a x ha).trans (u₃.agree_l I nv a x ha)))
    have aslot : M.PairMember I s A g₃ := (u₃.2 s A).mpr (Or.inr ⟨fun eq => ir ν (eq ▸ sν),
      (u₂.2 s A).mpr (Or.inr ⟨fun eq => ir τ (eq ▸ sτ),
        (u₁.2 s A).mpr (Or.inr ⟨fun eq => ir σ (eq ▸ sσ), (u₀.2 s A).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)⟩)
    have mslot : M.PairMember I σ μ.val g₃ := (u₃.2 σ μ.val).mpr (Or.inr ⟨fun eq => ir ν (eq ▸ σν),
      (u₂.2 σ μ.val).mpr (Or.inr ⟨fun eq => ir τ (eq ▸ hτ.predecessor_mem),
        (u₁.2 σ μ.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩)
    have eslot : M.PairMember I τ e.val g₃ := (u₃.2 τ e.val).mpr
      (Or.inr ⟨fun eq => ir ν (eq ▸ hν.predecessor_mem), (u₂.2 τ e.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
    have dslot : M.PairMember I ν D.val g₃ := (u₃.2 ν D.val).mpr (Or.inl ⟨rfl, rfl⟩)
    have tr (x y : (smdl_structure_l I (R := S) hn.2.1).Domain) :=
      sbin_agree_l I hZF hF hb hr hi hj hK hg ((hK g₃).mpr hg₃) agree x.property y.property (R := S)
    obtain ⟨B, C, fn, truth⟩ := (read' Y S K d g₃ hn ⟨A, hA⟩ D μ e ext hK ((hK g₃).mpr hg₃) aslot mslot eslot dslot).mp
      (transfer n₄ F₄ r₄ E K h₄.program h₄.root hE hK valid g₃ ((hK g₃).mpr hg₃))
      ⟨idx, fun x hx => sub x.val x.property hx⟩
      (fun x hx => (total x.val x.property hx).elim fun y hy => ⟨⟨y, hy.1⟩, (tr x ⟨y, hy.1⟩).mp hy.2⟩)
    exact ⟨B, C, fn, fun x y hxy => (tr x y).mpr (truth x y hxy)⟩
  exact ⟨move hm hn ex ey (fun _ _ _ _ _ hF hr hE hK => (hq.valid_l I hZF hω hm hn hF hr hE hK).mp),
    move hn hm ey ex (fun _ _ _ _ _ hF hr hE hK => (hq.valid_l I hZF hω hm hn hF hr hK hE).mpr)⟩

omit hZF in
/-- 固定定义域上的统一化证书直接产生该内部程序的实际函数。 -/
theorem Sc_uniform_d.raw_l {ω Y S K F n r i j g : M.Domain} (nx : ∃ x, M.mem x Y)
    (D : (smdl_structure_l I (R := S) nx).Domain) (source : Sc_uniform_d I ω Y S D.val)
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K)
    (total : ∀ x : (smdl_structure_l I (R := S) nx).Domain, M.PairMember I x.val D.val S →
      ∃ y : (smdl_structure_l I (R := S) nx).Domain, Sbin_d I Y S K F n r i j g x.val y.val) :
    ∃ B C : (smdl_structure_l I (R := S) nx).Domain, Fn0_d D C B ∧
      ∀ x y : (smdl_structure_l I (R := S) nx).Domain,
        Rd_entry_d x y B → Sbin_d I Y S K F n r i j g x.val y.val :=
  source nx K F n r i j g D.val hK hF hr hi hj hij hg D.property (fun _ _ h => h)
    (fun x hx ha => (total ⟨x, hx⟩ ha).elim fun y hy => ⟨y.val, y.property, hy⟩)

/-- 大集合上逐点存在已足够：追加成员守卫，在其余坐标仍产生源内的全定义代表。 -/
theorem Sc_uniform_d.on_l {ω Y S K F n r i j g : M.Domain}
    (hω : M.IsOmega ω) (nx : ∃ x, M.mem x Y)
    (D A : (smdl_structure_l I (R := S) nx).Domain) (source : Sc_uniform_d I ω Y S D.val)
    (hK : M.IsFunctionSpace I K ω Y) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hg : M.mem g K)
    (total : ∀ x : (smdl_structure_l I (R := S) nx).Domain, M.PairMember I x.val D.val S → M.PairMember I x.val A.val S →
      ∃ y : (smdl_structure_l I (R := S) nx).Domain, Sbin_d I Y S K F n r i j g x.val y.val) :
    ∃ B C : (smdl_structure_l I (R := S) nx).Domain, Fn0_d D C B ∧
      ∀ x y : (smdl_structure_l I (R := S) nx).Domain, Rd_entry_d x y B → M.PairMember I x.val A.val S →
        Sbin_d I Y S K F n r i j g x.val y.val := by
  obtain ⟨s, hs, hb, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun eq => ir i (eq ▸ his)
  have hsj : s ≠ j := fun eq => ir j (eq ▸ hjs)
  obtain ⟨m, G, build, atom⟩ := sfm_rel_l I hZF hω hF hi hs
  obtain ⟨l, H, k, step, implication⟩ := sfm_imp_l I hZF hω build.program build.root (build.span r hr)
  obtain ⟨g', update, hg'⟩ := senv_update_exists_l I hZF ((hK g).mp hg) hs A.property
  have hgK := (hK g').mpr hg'
  have point (x y : (smdl_structure_l I (R := S) nx).Domain) :
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
  obtain ⟨B, C, fn, truth⟩ := source.raw_l I nx D hK step.program step.root hi hj hij hgK (fun x hx => by
      classical
      by_cases hA : M.PairMember I x.val A.val S
      · obtain ⟨y, hy⟩ := total x hx hA
        exact ⟨y, (point x y).mpr (fun _ => hy)⟩
      · exact ⟨D, (point x D).mpr (fun h => (hA h).elim)⟩)
  exact ⟨B, C, fn, fun x y hxy => (point x y).mp (truth x y hxy)⟩

end YesMetaZFC.SetTheory.Internal
