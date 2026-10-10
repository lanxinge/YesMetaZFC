import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFinite
import YesMetaZFC.Model.SetTheory.Internal.SourceSmall
import YesMetaZFC.SetTheory.Collapse.EmbeddingFixed

/-! # 初等像中可数集合的逐元素回收

先反射源内的实际单射图，再用固定的自然数逐点回收其原像。
这给出可数集合的完整像方程，而非只有通常的单向包含。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.exists_delta_l {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    {n} (φ : Formula 1 (n+1)) (hc : φ.FreeClosed) (hd : φ.IsDelta0) (ρ η : Env M n)
    (hp : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j) :
    (∃ x, M.mem x X ∧ Formula.satisfies (ρ.push x) φ) ↔
      ∃ y, M.mem y Y ∧ Formula.satisfies (η.push y) φ := by
  have tr := hj.forall_delta_l hZF hω hX hY hm hn (.neg φ)
    (by simpa only [Definitional.Formula.FreeClosed] using hc) (.neg hd) ρ η hp
  constructor
  · rintro ⟨x, hx, hs⟩
    apply Classical.byContradiction
    intro no
    exact (Formula.satisfies_neg_iff _ _).mp
      (tr.mpr (fun y hy => (Formula.satisfies_neg_iff _ _).mpr (fun h => no ⟨y, hy, h⟩)) x hx) hs
  · rintro ⟨y, hy, hs⟩
    apply Classical.byContradiction
    intro no
    exact (Formula.satisfies_neg_iff _ _).mp
      (tr.mp (fun x hx => (Formula.satisfies_neg_iff _ _).mpr (fun h => no ⟨x, hx, h⟩)) y hy) hs

/-- 可数性见证属于目标时，其原像中有实际见证，且每个目标成员都有原像。 -/
theorem Smap_d.countable_preimage_l {ω c d X R Y S j A B ι : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hωX : M.mem ω X) (hAB : Rd_entry_d A B j) (hι : M.mem ι Y)
    (inj : M.IsSetInjectionFromTo I ι B ω) :
    ∃ f, M.mem f X ∧ M.IsSetInjectionFromTo I f A ω ∧
      ∀ b, M.mem b B → ∃ a, M.mem a A ∧ Rd_entry_d a b j := by
  have fix := hj.omega_l I hZF hω hX hY hm hn hωX
  -- 先反射一个实际单射；随后借固定的自然数逐点反射其原像。
  let φ : Formula 1 3 := .conj (fn0_m (.bound 1) (.bound 2) .newest) (sc_index_m (.bound 2) (.bound 1) .newest)
  let ρ (D : M.Domain) : Env M 2 := ⟨Fin.cases D (fun _ => ω), fun _ => D⟩
  have read D f : Formula.satisfies ((ρ D).push f) φ ↔ Fn0_d D ω f ∧ Sc_index_d ω D f := by
    simp only [φ, Formula.satisfies_conj_iff, fn0_sat_l hZF.1, sc_index_sat_l (ZF.modelsKP hZF)]; rfl
  obtain ⟨f, hf, spec⟩ := (hj.exists_delta_l hZF hω hX hY hm hn φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.conj (fn0_delta_l ..) (sc_index_delta_l ..)) (ρ A) (ρ B) (Fin.cases hAB (fun _ => fix))).mpr
      ⟨ι, hι, (read B ι).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) inj.1,
        Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) inj⟩⟩
  obtain ⟨fn, idx⟩ := (read A f).mp spec
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  have gn := (hj.function_l hZF hω hX hY hm hn hAB fix hfg).mp fn
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (sc_index_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (sc_index_delta_l ..)
    ⟨Fin.cases f (Fin.cases A (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases g (Fin.cases B (fun _ => ω)), fun _ => ω⟩ (Fin.cases hfg (Fin.cases hAB (fun _ => fix)))
  have gidx : Sc_index_d ω B g := (sc_index_sat_l (ZF.modelsKP hZF) ..).mp
    (tr.mp ((sc_index_sat_l (ZF.modelsKP hZF) ..).mpr idx))
  refine ⟨f, hf, ⟨fn0_function_l (ZF.modelsKP hZF) fn, fun a b n ha hb =>
    idx.injective a (fn.bound_l ha).1 b (fn.bound_l hb).1 n (fn.bound_l ha).2 ha hb⟩, fun b hb => ?_⟩
  obtain ⟨n, hnω, hbn⟩ := gn.2.1 b hb
  have hnfix := hj.natural_l hZF hω hX hY hm hn hωX n hnω
  have pull := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (Formula.existsMem (.bound 2) (rd_entry0_m .newest (.bound 2) (.bound 1)))
    (by simp -implicitDefEqProofs) (.existsMem _ (rd_entry0_delta_l ..))
    ⟨Fin.cases f (Fin.cases n (fun _ => A)), fun _ => A⟩
    ⟨Fin.cases g (Fin.cases n (fun _ => B)), fun _ => B⟩ (Fin.cases hfg (Fin.cases hnfix (fun _ => hAB)))
  simp only [Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] at pull
  obtain ⟨a, ha, han⟩ := pull.mpr ⟨b, hb, hbn⟩
  obtain ⟨b', _, hab⟩ := hj.1.1.2.2 a (hX A (hj.1.1.input_mem_of_pairMember hAB) a ha)
  have hbn' := (hj.entry_l hZF hω hX hY hm hn hab hnfix hfg).mp han
  exact ⟨a, ha, gidx.injective b' (gn.bound_l hbn').1 b hb n hnω hbn' hbn ▸ hab⟩

/-- 有序对属于初等像时，两个坐标也有实际原像。 -/
theorem Smap_d.kpair_preimage_l {ω c d X R Y S j p q x y : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : Rd_entry_d p q j) (pair : KPair_d M q x y) :
    ∃ a b, M.mem a X ∧ M.mem b X ∧ KPair_d M p a b ∧ Rd_entry_d a x j ∧ Rd_entry_d b y j := by
  let φ : Formula 1 2 := Formula.existsMem (.bound 1)
    (Formula.existsMem .newest (kpair0_m (.bound 3) (.bound 2) .newest))
  have read p a : Formula.satisfies ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push a) φ ↔
      ∃ t, M.mem t p ∧ ∃ b, M.mem b t ∧ KPair_d M p a b := by
    simp only [φ, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  have hxY := (pair.mem_l M hY (hj.1.1.output_mem_of_pairMember hp)).1
  obtain ⟨t, ht, hyt⟩ := (kpair_union_l M pair y).mpr (Or.inr rfl)
  obtain ⟨a, ha, spec⟩ := (hj.exists_delta_l hZF hω hX hY hm hn φ (by simp -implicitDefEqProofs [φ])
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ⟨fun _ => p, fun _ => p⟩ ⟨fun _ => q, fun _ => q⟩
    (fun _ => hp)).mpr ⟨x, hxY,
      (read q x).mpr ⟨t, ht, y, hyt, pair⟩⟩
  obtain ⟨_, _, b, _, code⟩ := (read p a).mp spec
  have hbX := (code.mem_l M hX (hj.1.1.input_mem_of_pairMember hp)).2
  obtain ⟨x', _, hx⟩ := hj.1.1.2.2 a ha
  obtain ⟨y', _, hy⟩ := hj.1.1.2.2 b hbX
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (kpair0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
    ⟨Fin.cases b (Fin.cases a (fun _ => p)), fun _ => p⟩
    ⟨Fin.cases y' (Fin.cases x' (fun _ => q)), fun _ => q⟩ (Fin.cases hy (Fin.cases hx (fun _ => hp)))
  have image := (kpair0_sat_l hZF.1 ..).mp (tr.mp ((kpair0_sat_l hZF.1 ..).mpr code))
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M image pair
  exact ⟨a, b, ha, hbX, code, hx, hy⟩

/-- 源内可数的传递集合被逐点固定，目标中也有它到 ω 的实际单射。 -/
theorem Smap_d.countable_fixed_l {ω c d X R Y S j A ι : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hωX : M.mem ω X) (hA : M.mem A X) (hAt : M.TransitiveSet A) (hι : M.mem ι X)
    (inj : M.IsSetInjectionFromTo I ι A ω) :
    Rd_entry_d A A j ∧ (∀ x, M.mem x A → Rd_entry_d x x j) ∧
      ∃ η, M.mem η Y ∧ M.IsSetInjectionFromTo I η A ω := by
  obtain ⟨B, _, hAB⟩ := hj.1.1.2.2 A hA
  obtain ⟨η, hη, hi⟩ := hj.1.1.2.2 ι hι
  have fix := hj.omega_l I hZF hω hX hY hm hn hωX
  let φ : Formula 1 3 := .conj (Formula.forallMem (.bound 1) (Formula.subset .newest (.bound 2)))
    (.conj (fn0_m (.bound 1) (.bound 2) .newest) (sc_index_m (.bound 2) (.bound 1) .newest))
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.conj (.forallMem _ (.atom ..)) (.conj (fn0_delta_l ..) (sc_index_delta_l ..)))
    ⟨Fin.cases ι (Fin.cases A (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases η (Fin.cases B (fun _ => ω)), fun _ => ω⟩ (Fin.cases hi (Fin.cases hAB (fun _ => fix)))
  simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_subset_iff, fn0_sat_l hZF.1, sc_index_sat_l (ZF.modelsKP hZF)] at tr
  obtain ⟨hBt, fn, idx⟩ := tr.mp ⟨hAt, fn0_of_function_l (ZF.modelsKP hZF) inj.1,
    Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF) inj⟩
  have count : M.IsSetInjectionFromTo I η B ω := ⟨fn0_function_l (ZF.modelsKP hZF) fn,
    fun a b n ha hb => idx.injective a (fn.bound_l ha).1 b (fn.bound_l hb).1 n (fn.bound_l ha).2 ha hb⟩
  obtain ⟨_, _, _, cover⟩ := hj.countable_preimage_l hZF hω hX hY hm hn hωX hAB hη count
  have rel x y u v (hx : Rd_entry_d x u j) (hy : Rd_entry_d y v j) : M.mem x y ↔ M.mem u v := by
    have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 2) (.mem (.bound (Fin.succ 0)) .newest)
      (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]) (.mem ..)
      ⟨Fin.cases y (fun _ => x), fun _ => x⟩ ⟨Fin.cases v (fun _ => u), fun _ => u⟩ (Fin.cases hy (fun _ => hx))
    simpa only [Formula.satisfies_mem_iff, Definitional.Term.newest, Term.eval_bound, Fin.cases_succ, Fin.cases_zero] using tr
  -- 可数性覆盖整个像；传递性及 Mostowski 唯一性固定其中每个元素。
  obtain ⟨_, point⟩ := mem_embedding_fixed_l hZF hX hj.1 rel hBt
    (fun x hx => (cover x hx).imp fun _ h => h.2)
  have eq : A = B := hZF.1.eq_of_same_members A B (fun x => ⟨fun hx => by
    obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x (hX A hA x hx)
    have hy := (rel x A y B hxy hAB).mp hx
    exact (hj.1.2 x y y hxy (point y hy)).symm ▸ hy,
    fun hx => (rel x A x B (point x hx) hAB).mpr hx⟩)
  subst B
  exact ⟨hAB, point, η, hη, count⟩

end YesMetaZFC.SetTheory.Internal
