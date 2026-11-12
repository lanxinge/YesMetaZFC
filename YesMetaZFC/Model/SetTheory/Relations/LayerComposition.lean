import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 原关系模型中的全部内部有限支撑

共同低层实现自然数的完整前驱；值可以是任意高层对象码。对背景内部的
编码公式作有限归纳，每步在原模型内追加一个有序对，得到实际函数码。
归纳覆盖非标准有限长度，不使用外部 ω 闭性或高层的传递坍塌。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
/-- 配对与并集足以追加新坐标，同时给出实际值域界。 -/
private theorem rf_append_l {N : Structure.{u}} (ext : Extensional N)
    (pair : ∀ a b : N.Domain, ∃ p, Pair_d N p a b)
    (union : ∀ a : N.Domain, ∃ b, N.IsUnionOf b a)
    {i j B f : N.Domain} (fn : Fn0_d i B f) (step : N.SuccessorOf j i) (irr : ¬ N.mem i i) (v : N.Domain) :
    ∃ B' g, Fn0_d j B' g ∧ ∀ x y, Rd_entry_d x y g ↔ Rd_entry_d x y f ∨ (x = i ∧ y = v) := by
  have insert (A x : N.Domain) : ∃ B, ∀ y, N.mem y B ↔ N.mem y A ∨ y = x := by
    obtain ⟨s, hs⟩ := pair x x
    obtain ⟨p, hp⟩ := pair A s
    obtain ⟨B, hb⟩ := union p
    refine ⟨B, fun y => (hb y).trans ?_⟩
    constructor
    · rintro ⟨z, hz, hy⟩
      rcases (hp z).mp hz with rfl | rfl
      · exact Or.inl hy
      · exact Or.inr (((hs y).mp hy).elim id id)
    · rintro (hy | eq)
      · exact ⟨A, (hp A).mpr (Or.inl rfl), hy⟩
      · subst y
        exact ⟨s, (hp s).mpr (Or.inr rfl), (hs x).mpr (Or.inl rfl)⟩
  obtain ⟨p, hp⟩ := (kpair_interpretation_l N ext pair).total i v
  obtain ⟨g, hg⟩ := insert f p
  obtain ⟨B', hb⟩ := insert B v
  have graph x y : Rd_entry_d x y g ↔ Rd_entry_d x y f ∨ (x = i ∧ y = v) := by
    constructor
    · rintro ⟨q, hq, hqg⟩
      rcases (hg q).mp hqg with old | rfl
      · exact Or.inl ⟨q, hq, old⟩
      · exact Or.inr (kpair_injective_l N hq hp)
    · rintro (⟨q, hq, hqf⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, hq, (hg q).mpr (Or.inl hqf)⟩
      · exact ⟨p, hp, (hg p).mpr (Or.inr rfl)⟩
  refine ⟨B', g, ⟨?_, ?_, ?_⟩, graph⟩
  · intro q hq
    rcases (hg q).mp hq with old | rfl
    · obtain ⟨x, hx, y, hy, pair⟩ := fn.1 q old
      exact ⟨x, (step x).mpr (Or.inl hx), y, (hb y).mpr (Or.inl hy), pair⟩
    · exact ⟨i, step.predecessor_mem, v, (hb v).mpr (Or.inr rfl), hp⟩
  · intro x hx
    rcases (step x).mp hx with old | eq
    · obtain ⟨y, hy, hxy⟩ := fn.2.1 x old
      exact ⟨y, (hb y).mpr (Or.inl hy), (graph x y).mpr (Or.inl hxy)⟩
    · have eq := ext.eq_of_same_members x i eq
      subst x
      exact ⟨v, (hb v).mpr (Or.inr rfl), (graph i v).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro x _ y _ z _ hy hz
    rcases (graph x y).mp hy with hy | hy <;> rcases (graph x z).mp hz with hz | hz
    · exact fn.2.2 x (fn.bound_l hy).1 y (fn.bound_l hy).2 z (fn.bound_l hz).2 hy hz
    · exact (irr (hz.1 ▸ (fn.bound_l hy).1)).elim
    · exact (irr (hy.1 ▸ (fn.bound_l hz).1)).elim
    · exact hy.2.trans hz.2.symm

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.finite_function_l {ω Γ Y S H k n a : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (pair : ∀ a b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain, ∃ p,
      Pair_d (smdl_structure_l I (R := S) ⟨H, layer.member⟩) p a b)
    (union : ∀ a : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain, ∃ b,
      (smdl_structure_l I (R := S) ⟨H, layer.member⟩).IsUnionOf b a)
    (hω : M.IsOmega ω) (inside : M.MemberSubset ω Γ) (hn : M.mem n ω) (ha : Fn0_d n Y a) :
    ∃ m f, Rd_entry_d n m k ∧ Rf_fun_d I Y S m f ∧ Rc_graph_d I Y S k f a := by
  let N := smdl_structure_l I (R := S) ⟨H, layer.member⟩
  let ρ : Env M 3 := ⟨Fin.cases k (Fin.cases S (fun _ => Y)), fun _ => Y⟩
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (fn0_m (.bound 1) (.bound 4) .newest)
      (.existsE (.existsE (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4))
        (.conj (rf_fun_m (𝒞 := kpair_convention_l) (.bound 6) (.bound 5) (.bound 1) .newest)
          (rc_graph_m (𝒞 := kpair_convention_l) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 2))))))) }
  have sat n : φ.denote ρ n ↔ ∀ a, Fn0_d n Y a →
      ∃ m f, Rd_entry_d n m k ∧ Rf_fun_d I Y S m f ∧ Rc_graph_d I Y S k f a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1, rf_fun_sat_l I, rc_graph_sat_l I hZF.1]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · intro z hz
      apply (sat z).mpr
      intro a ha
      obtain ⟨e, he, heω⟩ := hω.1.1
      have ze : z = e := hZF.1.eq_of_same_members z e (fun x => iff_of_false (hz x) (he x))
      obtain ⟨i, hi, hzi⟩ := layer.injection.1.2.2 z (inside z (ze ▸ heω))
      let i' : N.Domain := ⟨i, hi⟩
      have empty (x : N.Domain) : ¬ N.mem x i' := fun hx =>
        ((layer.predecessors z i hzi x.val).mp hx).elim fun y hy => hz y hy.1
      have fn : Fn0_d i' i' i' :=
        ⟨fun p hp => (empty p hp).elim, fun x hx => (empty x hx).elim, fun x hx => (empty x hx).elim⟩
      refine ⟨i, i, hzi, (rf_fun_native_l I _ ext i' i').mpr ⟨i', fn⟩, ?_⟩
      intro s x y hsx
      apply iff_of_false (fun h => hz s (ha.bound_l h).1)
      intro h
      obtain ⟨p, _, hp⟩ := (rf_val_native_l I _ ext
        ⟨x, layer.injection.1.output_mem_of_pairMember hsx⟩ ⟨y, (h.bounds_l I).2.1⟩ i').mp h
      exact empty p hp
    · intro n hn ih m hs
      apply (sat m).mpr
      intro a ha
      obtain ⟨g, hg⟩ := ZF.exists_restriction hZF I a n
      have fg := hg.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) ha)
        (fun x hx => (hs x).mpr (Or.inl hx))
      obtain ⟨i, f, hni, funf, graph⟩ := (sat n).mp ih g (fn0_of_function_l (ZF.modelsKP hZF) fg)
      let i' : N.Domain := ⟨i, layer.injection.1.output_mem_of_pairMember hni⟩
      let f' : N.Domain := ⟨f, funf.mem_l I⟩
      obtain ⟨B, fn⟩ := (rf_fun_native_l I _ ext i' f').mp funf
      obtain ⟨m₀, hm₀, hmω⟩ := hω.1.2 n hn
      have mm : m = m₀ := hs.eq hZF.1 hm₀
      have hm : M.mem m ω := mm ▸ hmω
      obtain ⟨j, hj, hmj⟩ := layer.injection.1.2.2 m (inside m hm)
      let j' : N.Domain := ⟨j, hj⟩
      have successor := layer.successor_l I hZF.1 ext i' j' hni hmj hs
      have irr : ¬ N.mem i' i' := by
        intro hi
        obtain ⟨s, hs, hsi⟩ := (layer.predecessors n i hni i).mp hi
        exact (KP.mem_irrefl_d (ZF.modelsKP hZF)) n ((layer.injection.2 s n i hsi hni) ▸ hs)
      obtain ⟨v, hv, hnv⟩ := ha.2.1 n hs.predecessor_mem
      let v' : N.Domain := ⟨v, hv⟩
      obtain ⟨B', b, fb, append⟩ := rf_append_l ext pair union fn successor irr v'
      have actual s y : Rd_entry_d s y a ↔ Rd_entry_d s y g ∨ (s = n ∧ y = v) := by
        constructor
        · intro h
          rcases (hs s).mp (ha.bound_l h).1 with old | eq
          · exact Or.inl ((hg.2 s y).mpr ⟨old, h⟩)
          · have eq := hZF.1.eq_of_same_members s n eq
            exact Or.inr ⟨eq, (fn0_function_l (ZF.modelsKP hZF) ha).1.2 n y v (eq ▸ h) hnv⟩
        · rintro (h | ⟨rfl, rfl⟩)
          · exact ((hg.2 s y).mp h).2
          · exact hnv
      refine ⟨j, b.val, hmj,
        (rf_fun_native_l I _ ext j' b).mpr ⟨B', fb⟩, ?_⟩
      intro s x y hsx
      by_cases hy : M.mem y Y
      · let x' : N.Domain := ⟨x, layer.injection.1.output_mem_of_pairMember hsx⟩
        let y' : N.Domain := ⟨y, hy⟩
        have same : (s = n ∧ y = v) ↔ (x' = i' ∧ y' = v') :=
          ⟨fun ⟨eq, ey⟩ => ⟨Subtype.ext (layer.injection.1.1.2 n x i (eq ▸ hsx) hni), Subtype.ext ey⟩,
            fun ⟨eq, ey⟩ => ⟨layer.injection.2 s n i ((show x = i from congrArg Subtype.val eq) ▸ hsx) hni,
              congrArg Subtype.val ey⟩⟩
        exact (actual s y).trans ((or_congr ((graph s x y hsx).trans
          (rf_val_native_l I _ ext x' y' f')) same).trans
          ((append x' y').symm.trans (rf_val_native_l I _ ext x' y' b).symm))
      · exact iff_of_false (fun h => hy (ha.bound_l h).2) (fun h => hy (h.bounds_l I).2.1)
  exact (sat n).mp (all n hn) a ha

/-- 完整定义域坐标把背景取值界读回原模型；高层值无需低层实现。 -/
theorem Rr_layer_d.function_range_l {Γ Y S H k D A g : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d a f : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hd : Rd_entry_d D d.val k) (fg : Fn0_d D A g)
    (bound : ∀ y, M.mem y A → Rd_entry_d y a.val S)
    (fn : Rf_fun_d I Y S d.val f.val) (graph : Rc_graph_d I Y S k f.val g) : Fn0_d d a f := by
  obtain ⟨B, hf⟩ := (rf_fun_native_l I _ ext d f).mp fn
  apply hf.retarget_l
  intro x y hxy
  obtain ⟨s, hs, hsx⟩ := (layer.predecessors D d.val hd x.val).mp (hf.bound_l hxy).1
  exact bound y.val (fg.bound_l ((graph s x.val y.val hsx).mpr
    ((rf_val_native_l I _ ext x y f).mpr hxy))).2

/-- 同一满定义域上的求值图唯一决定原模型函数码。 -/
theorem Rr_layer_d.function_unique_l {Γ Y S H k D g : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d f f' : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hd : Rd_entry_d D d.val k)
    (fn : Rf_fun_d I Y S d.val f.val) (fn' : Rf_fun_d I Y S d.val f'.val)
    (graph : Rc_graph_d I Y S k f.val g) (graph' : Rc_graph_d I Y S k f'.val g) : f = f' := by
  obtain ⟨B, hf⟩ := (rf_fun_native_l I _ ext d f).mp fn
  obtain ⟨B', hf'⟩ := (rf_fun_native_l I _ ext d f').mp fn'
  apply hf.ext_l ext hf'
  intro x hx
  obtain ⟨y, _, hxy⟩ := hf.2.1 x hx
  obtain ⟨s, _, hsx⟩ := (layer.predecessors D d.val hd x.val).mp hx
  exact ⟨y, hxy, (rf_val_native_l I _ ext x y f').mp ((graph' s x.val y.val hsx).mp
    ((graph s x.val y.val hsx).mpr ((rf_val_native_l I _ ext x y f).mpr hxy)))⟩

/-- 原模型函数沿满定义域坐标读成实际图；包含内部有限支撑的反向解码。 -/
theorem Rr_layer_d.function_decode_l {Γ Y S H k D A : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d a f : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hD : Rd_entry_d D d.val k) (fn : Fn0_d d a f)
    (carrier : ∀ x, M.mem x A ↔ M.mem x Y ∧ Rd_entry_d x a.val S) :
    ∃ g, Fn0_d D A g ∧ Rc_graph_d I Y S k f.val g := by
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k D
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo layer.injection.1
    (layer.transitive D (layer.injection.1.input_mem_of_pairMember hD)))
  have domain s x (hsx : Rd_entry_d s x t) := (layer.predecessors D d.val hD x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  obtain ⟨g, fg, read⟩ := smdl_function_l hZF ⟨H, layer.member⟩ ext d a f fn ft domain
  refine ⟨g, fg.retarget_l (fun s y hsy => ?_), ?_⟩
  · obtain ⟨x, hx, hsx⟩ := ft.2.1 s (fg.bound_l hsy).1
    exact (carrier y).mpr ⟨(fg.bound_l hsy).2,
      (fn.bound_l ((read s ⟨x, hx⟩ ⟨y, (fg.bound_l hsy).2⟩ hsx).mp hsy)).2⟩
  · intro s x y hsx
    by_cases hs : M.mem s D
    · by_cases hy : M.mem y Y
      · let x' : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain :=
          ⟨x, layer.injection.1.output_mem_of_pairMember hsx⟩
        let y' : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain := ⟨y, hy⟩
        exact (read s x' y' ((ht.2 s x).mpr ⟨hs, hsx⟩)).trans
          (rf_val_native_l I _ ext x' y' f).symm
      · exact iff_of_false (fun h => hy (fg.bound_l h).2) (fun h => hy (h.bounds_l I).2.1)
    · refine iff_of_false (fun h => hs (fg.bound_l h).1) (fun h => ?_)
      have native := (rf_val_native_l I _ ext ⟨x, layer.injection.1.output_mem_of_pairMember hsx⟩
        ⟨y, (h.bounds_l I).2.1⟩ f).mp h
      obtain ⟨r, hr, hrx⟩ := (layer.predecessors D d.val hD x).mp (fn.bound_l native).1
      exact hs (layer.injection.2 r s x hrx hsx ▸ hr)

/-- 同一满坐标图精确反映单射性，包括不在旧参数像内的内部函数码。 -/
theorem Rr_layer_d.function_injective_l {Γ Y S H k D g : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d a f : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hD : Rd_entry_d D d.val k) (fn : Fn0_d d a f) (fg : Fn0_d D Y g)
    (graph : Rc_graph_d I Y S k f.val g) :
    (∀ s t y, Rd_entry_d s y g → Rd_entry_d t y g → s = t) ↔
      ∀ x z y, Rd_entry_d x y f → Rd_entry_d z y f → x = z := by
  constructor
  · intro inj x z y hxy hzy
    obtain ⟨s, _, hsx⟩ := (layer.predecessors D d.val hD x.val).mp (fn.bound_l hxy).1
    obtain ⟨t, _, htz⟩ := (layer.predecessors D d.val hD z.val).mp (fn.bound_l hzy).1
    have eq := inj s t y.val
      ((graph s x.val y.val hsx).mpr ((rf_val_native_l I _ ext x y f).mpr hxy))
      ((graph t z.val y.val htz).mpr ((rf_val_native_l I _ ext z y f).mpr hzy))
    exact Subtype.ext (layer.injection.1.1.2 t x.val z.val (eq ▸ hsx) htz)
  · intro inj s t y hsy hty
    have hDΓ := layer.injection.1.input_mem_of_pairMember hD
    obtain ⟨x, hx, hsx⟩ := layer.injection.1.2.2 s (layer.transitive D hDΓ s (fg.bound_l hsy).1)
    obtain ⟨z, hz, htz⟩ := layer.injection.1.2.2 t (layer.transitive D hDΓ t (fg.bound_l hty).1)
    let y' : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain := ⟨y, (fg.bound_l hsy).2⟩
    have eq : x = z := congrArg Subtype.val (inj ⟨x, hx⟩ ⟨z, hz⟩ y'
      ((rf_val_native_l I _ ext ⟨x, hx⟩ y' f).mp ((graph s x y hsx).mp hsy))
      ((rf_val_native_l I _ ext ⟨z, hz⟩ y' f).mp ((graph t z y htz).mp hty)))
    exact layer.injection.2 s t z (eq ▸ hsx) htz

/-- 背景有限重排先编码成原函数，再逐坐标读回同一支撑复合方程。 -/
theorem Rr_layer_d.factor_l {ω Γ Y S H k m n r L A B : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (pair : ∀ a b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain, ∃ p,
      Pair_d (smdl_structure_l I (R := S) ⟨H, layer.member⟩) p a b)
    (union : ∀ a : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain, ∃ b,
      (smdl_structure_l I (R := S) ⟨H, layer.member⟩).IsUnionOf b a)
    (hω : M.IsOmega ω) (inside : M.MemberSubset ω Γ) (hm : M.mem m ω)
    (m' n' ℓ a b : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hmm : Rd_entry_d m m'.val k) (hnn : Rd_entry_d n n'.val k)
    (length : ∀ x, M.mem x L ↔ M.mem x Y ∧ Rd_entry_d x ℓ.val S)
    (fr : Fn0_d m n r) (comp : Cp0_d m n L r A B) (fb : Fn0_d m' ℓ b)
    (ga : Rc_graph_d I Y S k a.val A) (gb : Rc_graph_d I Y S k b.val B) :
    ∃ q : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain,
      Fn0_d m' n' q ∧ Cp0_d m' n' ℓ q a b := by
  let N₀ := smdl_structure_l I (R := S) ⟨H, layer.member⟩
  have fk := fn0_of_function_l (ZF.modelsKP hZF) layer.injection.1
  have fr' := fr.mono_target_l (layer.transitive n (layer.injection.1.input_mem_of_pairMember hnn))
  obtain ⟨v, cv⟩ := cp0_exists_l (ZF.modelsKP hZF) fr' fk
  obtain ⟨m₀, q₀, hmm₀, fn, gq⟩ := layer.finite_function_l hZF ext pair union hω inside hm cv.1
  have eq := layer.injection.1.1.2 m m₀ m'.val hmm₀ hmm
  subst m₀
  let q : N₀.Domain := ⟨q₀, fn.mem_l I⟩
  obtain ⟨C, fq⟩ := (rf_fun_native_l I _ ext m' q).mp fn
  have qn : Fn0_d m' n' q := fq.retarget_l (fun x y hxy => by
    obtain ⟨i, hi, hix⟩ := (layer.predecessors m m'.val hmm x.val).mp (fq.bound_l hxy).1
    have hiy := (gq i x.val y.val hix).mpr ((rf_val_native_l I _ ext x y q).mpr hxy)
    obtain ⟨j, _, z, hz, hij, hjz, hiz⟩ := cv.2 i hi
    have eq := cv.1.2.2 i hi z hz y.val y.property hiz hiy
    exact (layer.predecessors n n'.val hnn y.val).mpr ⟨j, (fr.bound_l hij).2, eq ▸ hjz⟩)
  refine ⟨q, qn, fb, fun i hi => ?_⟩
  obtain ⟨s, hs, hsi⟩ := (layer.predecessors m m'.val hmm i.val).mp hi
  obtain ⟨t, ht, x, hx, hst, htx, hsx⟩ := comp.2 s hs
  obtain ⟨j, hj, htj⟩ := layer.injection.1.2.2 t
    (layer.transitive n (layer.injection.1.input_mem_of_pairMember hnn) t ht)
  let j' : N₀.Domain := ⟨j, hj⟩
  let x' : N₀.Domain := ⟨x, ((length x).mp hx).1⟩
  exact ⟨j', (layer.predecessors n n'.val hnn j).mpr ⟨t, ht, htj⟩, x', ((length x).mp hx).2,
    (rf_val_native_l I _ ext i j' q).mp ((gq s i.val j hsi).mp ((cv.value_l fr' fk hst).mpr htj)),
    (rf_val_native_l I _ ext j' x' a).mp ((ga t j x htj).mp htx),
    (rf_val_native_l I _ ext i x' b).mp ((gb s i.val x hsi).mp hsx)⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 全部有限支撑与原模型函数码的实际双射

背景内部有限图先在原模型内编码；反向沿自然数的满坐标图解码。
唯一性给出一张实际集合图，满射性覆盖原模型的全部有限函数，单射性
判定也被精确反映。支撑值可以在高层，不要求原模型传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Rr_finite_d (ω L X R k g f : M.Domain) : Prop := ∃ n m,
  M.mem n ω ∧ Fn0_d n L g ∧ Rd_entry_d n m k ∧ Rf_fun_d I X R m f ∧ Rc_graph_d I X R k f g

def rr_finite_m {d} (ω L X R k g f : Term d) : Formula 1 d := set[d] ⟪
  ∃ n m, n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜g⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(n, m, ⌜k⌝ₛ) ∧
    ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, m, ⌜f⌝ₛ) ∧
    ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜k⌝ₛ, ⌜f⌝ₛ, ⌜g⌝ₛ)⟫
derive_free_closed rr_finite_m

theorem rr_finite_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L X R k g f : Term d) :
    Formula.satisfies ρ (rr_finite_m ω L X R k g f) ↔
      Rr_finite_d I (ω.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (k.eval ρ) (g.eval ρ) (f.eval ρ) := by
  simp only [rr_finite_m, Rr_finite_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry0_sat_l hE, rf_fun_sat_l I, rc_graph_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定两端实际函数，有限编码自动确定其原定义域对应。 -/
theorem Rr_finite_d.domain_l (hE : Extensional M) {ω L X R z a n : M.Domain}
    (nx : ∃ x, M.mem x X) (ext : Extensional (smdl_structure_l I (R := R) nx))
    (m B f : (smdl_structure_l I (R := R) nx).Domain)
    (fa : Fn0_d n L a) (fn : Fn0_d m B f) (code : Rr_finite_d I ω L X R z a f.val) :
    M.mem n ω ∧ Rd_entry_d n m.val z := by
  obtain ⟨n', m', hn, fa', hnm, ff, _⟩ := code
  have eq := fa'.domain_eq_l hE fa
  subst n'
  obtain ⟨C, fn'⟩ := (rf_fun_native_l I nx ext ⟨m', ff.1⟩ f).mp ff
  exact ⟨hn, (show m' = m.val from congrArg Subtype.val (fn'.domain_eq_l ext fn)) ▸ hnm⟩

theorem Rr_finite_d.unique_l {ω Γ X R H k L g f f' : M.Domain}
    (layer : Rr_layer_d Kp Γ X R H k)
    (ext : Extensional (smdl_structure_l Kp (R := R) ⟨H, layer.member⟩))
    (h : Rr_finite_d Kp ω L X R k g f) (h' : Rr_finite_d Kp ω L X R k g f') : f = f' := by
  obtain ⟨n, m, _, fg, hn, fn, graph⟩ := h
  obtain ⟨n', m', _, fg', hn', fn', graph'⟩ := h'
  have eq := fg'.domain_eq_l hZF.1 fg
  subst n'
  have eq := layer.injection.1.1.2 n m' m hn' hn
  subst m'
  exact congrArg Subtype.val (layer.function_unique_l hZF ext
    ⟨m, layer.injection.1.output_mem_of_pairMember hn⟩ ⟨f, fn.mem_l Kp⟩ ⟨f', fn'.mem_l Kp⟩ hn fn fn' graph graph')


/-- 同一原函数码也唯一确定背景有限支撑；定义域之外由自然数坐标排除。 -/
theorem Rr_finite_d.input_unique_l {ω L X R H k a b f : M.Domain}
    (numbers : Rr_layer_d Kp ω X R H k)
    (h : Rr_finite_d Kp ω L X R k a f) (h' : Rr_finite_d Kp ω L X R k b f) : a = b := by
  obtain ⟨m, m', _, fa, hm, _, ga⟩ := h
  obtain ⟨n, n', _, fb, hn, _, gb⟩ := h'
  apply (fn0_function_l (ZF.modelsKP hZF) fa).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) fb).1.1
  intro i x
  by_cases hi : M.mem i ω
  · obtain ⟨j, _, hij⟩ := numbers.injection.1.2.2 i hi
    exact (ga i j x hij).trans (gb i j x hij).symm
  · exact iff_of_false
      (fun h => hi (numbers.transitive m (numbers.injection.1.input_mem_of_pairMember hm) i (fa.bound_l h).1))
      (fun h => hi (numbers.transitive n (numbers.injection.1.input_mem_of_pairMember hn) i (fb.bound_l h).1))


/-- 指定原生有限空间的全部成员，与全部背景内部有限图形成规范双射。 -/
theorem Rr_layer_d.finite_codes_l {ω X R w k : M.Domain}
    (layer : Rr_layer_d Kp ω X R w k)
    (ext : Extensional (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩))
    (pair : ∀ a b : (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩).Domain, ∃ p,
      Pair_d (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩) p a b)
    (union : ∀ a : (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩).Domain, ∃ b,
      (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩).IsUnionOf b a)
    (hω : M.IsOmega ω)
    (a B : (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩).Domain)
    (finite : Sc_fseq_d Kp w a.val B.val X R) : ∃ L J C p,
      (∀ x, M.mem x L ↔ M.mem x X ∧ Rd_entry_d x a.val R) ∧ Fseq_space_d Kp ω L J ∧
      (∀ f, M.mem f C ↔ M.mem f X ∧ Rd_entry_d f B.val R) ∧ M.IsSetBijectionFromTo Kp p J C ∧
      (∀ g f, Rd_entry_d g f p ↔ Rr_finite_d Kp ω L X R k g f) ∧
      ∀ g (f : (smdl_structure_l Kp (R := R) ⟨w, layer.member⟩).Domain), Rd_entry_d g f.val p →
        ((∀ s t y, Rd_entry_d s y g → Rd_entry_d t y g → s = t) ↔
          ∀ x z y, Rd_entry_d x y f → Rd_entry_d z y f → x = z) := by
  let N := smdl_structure_l Kp (R := R) ⟨w, layer.member⟩
  have nativeSpace := (sc_fseq_native_l Kp ⟨w, layer.member⟩ ext ⟨w, layer.member⟩ a B).mp finite
  let η : Env M 2 := ⟨Fin.cases a.val (fun _ => R), fun _ => X⟩
  let ψ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨L, ls⟩ := ZF.separation_exists_d hZF ψ η X
  have length x : M.mem x L ↔ M.mem x X ∧ Rd_entry_d x a.val R :=
    (ls x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨J, space⟩ := ZF.fseq_space_exists_l Kp hZF hω L
  let η' : Env M 2 := ⟨Fin.cases B.val (fun _ => R), fun _ => X⟩
  obtain ⟨C, cs⟩ := ZF.separation_exists_d hZF ψ η' X
  have carrier f : M.mem f C ↔ M.mem f X ∧ Rd_entry_d f B.val R :=
    (cs f).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  let ρ : Env M 5 := ⟨Fin.cases k (Fin.cases R (Fin.cases X (Fin.cases L (fun _ => ω)))), fun _ => X⟩
  let φ : BinarySchema 5 := {
    body := rr_finite_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat g f : φ.denote ρ g f ↔ Rr_finite_d Kp ω L X R k g f := rr_finite_sat_l Kp hZF.1 ..
  have total g (hg : M.mem g J) : ∃ f, φ.denote ρ g f := by
    obtain ⟨n, hn, fg⟩ := (space g).mp hg
    have fg := fn0_of_function_l (ZF.modelsKP hZF) fg
    obtain ⟨m, f, hm, fn, graph⟩ := layer.finite_function_l hZF ext pair union hω (fun _ h => h) hn
      (fg.mono_target_l (fun x hx => ((length x).mp hx).1))
    exact ⟨f, (sat g f).mpr ⟨n, m, hn, fg, hm, fn, graph⟩⟩
  have unique g (_ : M.mem g J) f f' (hf : φ.denote ρ g f) (hf' : φ.denote ρ g f') : f = f' :=
    ((sat g f).mp hf).unique_l hZF layer ext ((sat g f').mp hf')
  have values g f (h : Rr_finite_d Kp ω L X R k g f) : M.mem f C := by
    obtain ⟨n, m, hn, fg, hm, fn, graph⟩ := h
    let m' : N.Domain := ⟨m, layer.injection.1.output_mem_of_pairMember hm⟩
    let f' : N.Domain := ⟨f, fn.mem_l Kp⟩
    have native := layer.function_range_l hZF ext m' a f' hm fg
      (fun x hx => ((length x).mp hx).2) fn graph
    exact (carrier f).mpr ⟨f'.property, (nativeSpace f').mpr ⟨m',
      (layer.image m).mpr ⟨n, hn, hm⟩, native⟩⟩
  obtain ⟨p, fp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ total unique
    (fun g f _ h => values g f ((sat g f).mp h))
  have graph g f : Rd_entry_d g f p ↔ Rr_finite_d Kp ω L X R k g f := by
    apply (ps g f).trans
    refine ⟨fun h => (sat g f).mp h.2, fun h => ?_⟩
    have code := h
    obtain ⟨n, _, hn, fg, _⟩ := code
    exact ⟨(space g).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fg⟩, (sat g f).mpr h⟩
  have injective : M.IsSetInjective Kp p := by
    intro g h f hgf hhf
    obtain ⟨m, _, hm, fg, _, _, gg⟩ := (graph g f).mp hgf
    obtain ⟨n, _, hn, fh, _, _, gh⟩ := (graph h f).mp hhf
    apply (fn0_function_l (ZF.modelsKP hZF) fg).1.1.eq_of_pairMember_iff hZF.1
      (fn0_function_l (ZF.modelsKP hZF) fh).1.1
    intro s y
    by_cases hs : M.mem s ω
    · obtain ⟨x, _, hsx⟩ := layer.injection.1.2.2 s hs
      exact (gg s x y hsx).trans (gh s x y hsx).symm
    · exact iff_of_false (fun h => hs (layer.transitive m hm s (fg.bound_l h).1))
        (fun h => hs (layer.transitive n hn s (fh.bound_l h).1))
  have onto : M.IsSetSurjectiveOnto Kp p J C := by
    intro f hf
    obtain ⟨hfx, hfB⟩ := (carrier f).mp hf
    let f' : N.Domain := ⟨f, hfx⟩
    obtain ⟨m, hm, ff⟩ := (nativeSpace f').mp hfB
    obtain ⟨n, hn, hnm⟩ := (layer.image m.val).mp hm
    obtain ⟨g, fg, decode⟩ := layer.function_decode_l hZF ext m a f' hnm ff length
    exact ⟨g, (space g).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fg⟩,
      (graph g f).mpr ⟨n, m.val, hn, fg, hnm, (rf_fun_native_l Kp _ ext m f').mpr ⟨a, ff⟩, decode⟩⟩
  refine ⟨L, J, C, p, length, space, carrier, ⟨⟨fp, injective⟩, onto⟩, graph, ?_⟩
  intro g f hgf
  obtain ⟨n, m, _, fg, hm, fn, decode⟩ := (graph g f.val).mp hgf
  let m' : N.Domain := ⟨m, layer.injection.1.output_mem_of_pairMember hm⟩
  have native := layer.function_range_l hZF ext m' a f hm fg
    (fun x hx => ((length x).mp hx).2) fn decode
  exact layer.function_injective_l hZF ext m' a f hm native
    (fg.mono_target_l (fun x hx => ((length x).mp hx).1)) decode

end YesMetaZFC.SetTheory.Internal

/-! ## 有限支撑复制与原函数码的像

原自然数坐标先与初等图交换。支撑的实际逐点像因此决定原函数码的像；
证明覆盖背景的全部内部有限长度，不把函数码对应作为额外参数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 搬运原函数码后，完整自然数坐标直接给出目标支撑的编码。 -/
theorem Rr_finite_d.image_l {ω c X R c' Y S q w v z t L L' n a a' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S)
    (map : Smap_d I ω c c' X Y q) (ext : Rf_ext_d I X R)
    (source : Rr_layer_d I ω X R w z) (target : Rr_layer_d I ω Y S v t)
    (fa : Fn0_d n L a) (fa' : Fn0_d n L' a')
    (assign : Smap_assign_d I n q a a')
    (code : Rr_finite_d I ω L X R z a f) (hff : Rd_entry_d f f' q) :
    Rr_finite_d I ω L' Y S t a' f' := by
  obtain ⟨n₀, m, hn, fa₀, hnm, ff, graph⟩ := code
  have eq := fa₀.domain_eq_l hZF.1 fa
  subst n₀
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have numbers := (source.omega_map_l I hZF hω mx my map ext ext' target).2
  obtain ⟨m', hm', hnm'⟩ := target.injection.1.2.2 n hn
  have hmm := numbers n m m' hnm hnm'
  have ey := ext'.native_l I my.2.1
  have ff' := ff.map_l I hZF hω mx my map hmm hff
  have forward i x y (hix : Rd_entry_d i x t) (hiy : Rd_entry_d i y a') : Rf_val_d I Y S x y f' := by
    have hi := (fa'.bound_l hiy).1
    obtain ⟨s, _, his⟩ := source.injection.1.2.2 i (hω.transitive (ZF.modelsKP hZF) n hn i hi)
    obtain ⟨u, _, hiu⟩ := fa.2.1 i hi
    have value := (graph i s u his).mp hiu
    obtain ⟨u', _, huu⟩ := map.1.1.2.2 u (value.bounds_l I).2.1
    have eq := fa'.2.2 i hi u' (fa'.bound_l (assign i hi u u' hiu huu)).2 y (fa'.bound_l hiy).2
      (assign i hi u u' hiu huu) hiy
    exact eq ▸ value.map_l I hZF hω mx my map (numbers i s x his hix) huu hff
  refine ⟨n, m', hn, fa', hnm', ff', fun i x y hix => ⟨forward i x y hix, ?_⟩⟩
  intro value
  let F' : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨f', ff'.mem_l I⟩
  obtain ⟨B, fn⟩ := (rf_fun_native_l I my.2.1 ey ⟨m', hm'⟩ F').mp ff'
  have hx := (fn.bound_l ((rf_val_native_l I my.2.1 ey ⟨x, (value.bounds_l I).1⟩
    ⟨y, (value.bounds_l I).2.1⟩ F').mp value)).1
  obtain ⟨j, hj, hjx⟩ := (target.predecessors n m' hnm' x).mp hx
  have hi : M.mem i n := target.injection.2 j i x hjx hix ▸ hj
  obtain ⟨u, _, hiu⟩ := fa'.2.1 i hi
  exact ff'.unique_l I ext' (forward i x u hix hiu) value ▸ hiu

theorem Rr_finite_d.map_l {ω c X R c' Y S q w v z t L L' n a a' f f' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I c' Y S)
    (map : Smap_d I ω c c' X Y q) (ext : Rf_ext_d I X R)
    (source : Rr_layer_d I ω X R w z) (target : Rr_layer_d I ω Y S v t)
    (fa : Fn0_d n L a) (fa' : Fn0_d n L' a')
    (assign : Smap_assign_d I n q a a')
    (code : Rr_finite_d I ω L X R z a f) (code' : Rr_finite_d I ω L' Y S t a' f') :
    Rd_entry_d f f' q := by
  have hf := code.elim fun _ h => h.elim fun _ h => h.2.2.2.1.mem_l I
  obtain ⟨g, _, hfg⟩ := map.1.1.2.2 f hf
  have next := code.image_l hZF hω mx my map ext source target fa fa' assign hfg
  have ext' : Rf_ext_d I Y S := map.extensional_l hZF hω mx my ext
  have eq := next.unique_l hZF target (ext'.native_l I _) code'
  exact eq ▸ hfg

end YesMetaZFC.SetTheory.Internal

/-! ## 沿定义域和值域的完整解释回读实际函数

两份完整前驱图同时回读参数和函数值。所得背景函数保留全部求值方程，
不要求原模型传递，也不把原字母表的对象码误作背景字母。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.function_pull_l {Γ B X R H V z t D A : M.Domain}
    (domain : Rr_layer_d I Γ X R H z) (range : Rr_layer_d I B X R V t)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨H,domain.member⟩))
    (d a f : (smdl_structure_l I (R := R) ⟨H,domain.member⟩).Domain)
    (hD : Rd_entry_d D d.val z) (hA : Rd_entry_d A a.val t) (fn : Fn0_d d a f) :
    ∃ g, Fn0_d D A g ∧ ∀ i n x y, Rd_entry_d i n z → Rd_entry_d x y t →
      (Rd_entry_d i x g ↔ Rf_val_d I X R n y f.val) := by
  let N := smdl_structure_l I (R := R) ⟨H,domain.member⟩
  let ρ : Env M 5 := ⟨fun i => [X,R,z,t,f.val].get i,fun _ => H⟩
  let φ : BinarySchema 5 := { body := .existsE (.existsE
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 6))
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 7))
        (rf_val_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 5) (.bound 1) .newest (.bound 8))))) }
  have read (i x : M.Domain) : φ.denote ρ i x ↔ ∃ n y,
      Rd_entry_d i n z ∧ Rd_entry_d x y t ∧ Rf_val_d I X R n y f.val := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,rf_val_sat_l I]
    rfl
  have total (i : M.Domain) (hi : M.mem i D) : ∃ x, φ.denote ρ i x := by
    obtain ⟨n,hn,hin⟩ := domain.injection.1.2.2 i
      (domain.transitive D (domain.injection.1.input_mem_of_pairMember hD) i hi)
    have member : N.mem ⟨n,hn⟩ d := (domain.predecessors D d.val hD n).mpr ⟨i,hi,hin⟩
    obtain ⟨y,hy,hny⟩ := fn.2.1 ⟨n,hn⟩ member
    obtain ⟨x,hx,hxy⟩ := (range.predecessors A a.val hA y.val).mp hy
    exact ⟨x,(read i x).mpr ⟨n,y.val,hin,hxy,(rf_val_native_l I _ ext ⟨n,hn⟩ y f).mpr hny⟩⟩
  have unique (i : M.Domain) (_ : M.mem i D) (x x' : M.Domain)
      (hx : φ.denote ρ i x) (hx' : φ.denote ρ i x') : x = x' := by
    obtain ⟨n,y,hin,hxy,val⟩ := (read i x).mp hx
    obtain ⟨n',y',hin',hxy',val'⟩ := (read i x').mp hx'
    have eq := domain.injection.1.1.2 i n' n hin' hin
    subst n'
    let n₀ : N.Domain := ⟨n,domain.injection.1.output_mem_of_pairMember hin⟩
    let y₀ : N.Domain := ⟨y,range.injection.1.output_mem_of_pairMember hxy⟩
    let y₁ : N.Domain := ⟨y',range.injection.1.output_mem_of_pairMember hxy'⟩
    have v₀ := (rf_val_native_l I _ ext n₀ y₀ f).mp val
    have v₁ := (rf_val_native_l I _ ext n₀ y₁ f).mp val'
    have eq : y = y' := congrArg Subtype.val
      (fn.2.2 n₀ (fn.bound_l v₀).1 y₀ (fn.bound_l v₀).2 y₁ (fn.bound_l v₁).2 v₀ v₁)
    exact range.injection.2 x x' y' (eq ▸ hxy) hxy'
  have values (i x : M.Domain) (_ : M.mem i D) (hx : φ.denote ρ i x) : M.mem x A := by
    obtain ⟨n,y,hin,hxy,val⟩ := (read i x).mp hx
    have native := (rf_val_native_l I _ ext
      ⟨n,domain.injection.1.output_mem_of_pairMember hin⟩
      ⟨y,range.injection.1.output_mem_of_pairMember hxy⟩ f).mp val
    obtain ⟨x',hx',hx'y⟩ := (range.predecessors A a.val hA y).mp (fn.bound_l native).2
    exact (range.injection.2 x' x y hx'y hxy) ▸ hx'
  obtain ⟨g,fg,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique values
  refine ⟨g,fn0_of_function_l (ZF.modelsKP hZF) fg,?_⟩
  intro i n x y hin hxy
  constructor
  · intro hix
    obtain ⟨n',y',hin',hxy',val⟩ := (read i x).mp ((graph i x).mp hix).2
    have en := domain.injection.1.1.2 i n' n hin' hin
    have ey := range.injection.1.1.2 x y' y hxy' hxy
    exact en ▸ ey ▸ val
  · intro val
    have native := (rf_val_native_l I _ ext
      ⟨n,domain.injection.1.output_mem_of_pairMember hin⟩
      ⟨y,range.injection.1.output_mem_of_pairMember hxy⟩ f).mp val
    obtain ⟨i',hi',hi'n⟩ := (domain.predecessors D d.val hD n).mp (fn.bound_l native).1
    have hi : M.mem i D := (domain.injection.2 i' i n hi'n hin) ▸ hi'
    exact (graph i x).mpr ⟨hi,(read i x).mpr ⟨n,y,hin,hxy,val⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 沿实际字母双射回读原生有限函数

数字仍由完整数字图解释；字母只需原对象成员集与外部字母表之间的实际双射。
函数值的唯一原像直接给出外部函数，不要求字母属于任何背景传递秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.function_pull_alphabet_l {Γ D X R H z A B t : M.Domain}
    (domain : Rr_layer_d I Γ X R H z)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨H,domain.member⟩))
    (d a f : (smdl_structure_l I (R := R) ⟨H,domain.member⟩).Domain)
    (hD : Rd_entry_d D d.val z) (fn : Fn0_d d a f)
    (carrier : ∀ y, M.mem y B ↔ M.mem y X ∧ Rd_entry_d y a.val R)
    (letters : M.IsSetBijectionFromTo I t A B) :
    ∃ g, Fn0_d D A g ∧ ∀ i n x y, Rd_entry_d i n z → Rd_entry_d x y t →
      (Rd_entry_d i x g ↔ Rf_val_d I X R n y f.val) := by
  let N := smdl_structure_l I (R := R) ⟨H,domain.member⟩
  let ρ : Env M 5 := ⟨fun i => [X,R,z,t,f.val].get i,fun _ => H⟩
  let φ : BinarySchema 5 := { body := .existsE (.existsE
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 6))
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 7))
        (rf_val_m (𝒞 := kpair_convention_l) (.bound 4) (.bound 5) (.bound 1) .newest (.bound 8))))) }
  have read i x : φ.denote ρ i x ↔ ∃ n y,
      Rd_entry_d i n z ∧ Rd_entry_d x y t ∧ Rf_val_d I X R n y f.val := by
    simp only [φ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1,rf_val_sat_l I]; rfl
  have total i (hi : M.mem i D) : ∃ x, φ.denote ρ i x := by
    obtain ⟨n,hn,hin⟩ := domain.injection.1.2.2 i
      (domain.transitive D (domain.injection.1.input_mem_of_pairMember hD) i hi)
    have member : N.mem ⟨n,hn⟩ d := (domain.predecessors D d.val hD n).mpr ⟨i,hi,hin⟩
    obtain ⟨y,hy,hny⟩ := fn.2.1 ⟨n,hn⟩ member
    obtain ⟨x,_,hxy⟩ := letters.2 y.val ((carrier y.val).mpr ⟨y.property,hy⟩)
    exact ⟨x,(read i x).mpr ⟨n,y.val,hin,hxy,(rf_val_native_l I _ ext ⟨n,hn⟩ y f).mpr hny⟩⟩
  have unique i (_ : M.mem i D) x x' (hx : φ.denote ρ i x) (hx' : φ.denote ρ i x') : x = x' := by
    obtain ⟨n,y,hin,hxy,val⟩ := (read i x).mp hx
    obtain ⟨n',y',hin',hxy',val'⟩ := (read i x').mp hx'
    have eq := domain.injection.1.1.2 i n' n hin' hin
    subst n'
    let n₀ : N.Domain := ⟨n,domain.injection.1.output_mem_of_pairMember hin⟩
    let y₀ : N.Domain := ⟨y,((carrier y).mp (letters.1.1.output_mem_of_pairMember hxy)).1⟩
    let y₁ : N.Domain := ⟨y',((carrier y').mp (letters.1.1.output_mem_of_pairMember hxy')).1⟩
    have v₀ := (rf_val_native_l I _ ext n₀ y₀ f).mp val
    have v₁ := (rf_val_native_l I _ ext n₀ y₁ f).mp val'
    have eq : y = y' := congrArg Subtype.val
      (fn.2.2 n₀ (fn.bound_l v₀).1 y₀ (fn.bound_l v₀).2 y₁ (fn.bound_l v₁).2 v₀ v₁)
    exact letters.1.2 x x' y' (eq ▸ hxy) hxy'
  have values i x (_ : M.mem i D) (hx : φ.denote ρ i x) : M.mem x A := by
    obtain ⟨_,_,_,hxy,_⟩ := (read i x).mp hx
    exact letters.1.1.input_mem_of_pairMember hxy
  obtain ⟨g,fg,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique values
  refine ⟨g,fn0_of_function_l (ZF.modelsKP hZF) fg,?_⟩
  intro i n x y hin hxy
  constructor
  · intro hix
    obtain ⟨n',y',hin',hxy',val⟩ := (read i x).mp ((graph i x).mp hix).2
    exact domain.injection.1.1.2 i n' n hin' hin ▸ letters.1.1.1.2 x y' y hxy' hxy ▸ val
  · intro val
    have native := (rf_val_native_l I _ ext
      ⟨n,domain.injection.1.output_mem_of_pairMember hin⟩
      ⟨y,((carrier y).mp (letters.1.1.output_mem_of_pairMember hxy)).1⟩ f).mp val
    obtain ⟨i',hi',hi'n⟩ := (domain.predecessors D d.val hD n).mp (fn.bound_l native).1
    exact (graph i x).mpr ⟨domain.injection.2 i' i n hi'n hin ▸ hi',(read i x).mpr ⟨n,y,hin,hxy,val⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整共同层上的图原子与高值域复合

低层图原子和复合按同一有界公式读取。高层支撑只沿其定义域坐标
读取函数值，因而复合的双向保持不要求支撑值属于共同层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.entry_l {Γ Y S H k A B F : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (a b f : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hA : Rd_entry_d A a.val k) (hB : Rd_entry_d B b.val k) (hF : Rd_entry_d F f.val k) :
    Rd_entry_d A B F ↔ Rd_entry_d a b f := by
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨A, layer.injection.1.input_mem_of_pairMember hA⟩⟩
  have read := rr_realize_delta_l I layer.transitive nx ⟨H, layer.member⟩
    layer.injection layer.predecessors (rd_entry0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨Fin.cases ⟨F, layer.injection.1.input_mem_of_pairMember hF⟩
      (Fin.cases ⟨B, layer.injection.1.input_mem_of_pairMember hB⟩
        (fun _ => ⟨A, layer.injection.1.input_mem_of_pairMember hA⟩)), fun _ => ⟨A, layer.injection.1.input_mem_of_pairMember hA⟩⟩ :
      Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases f (Fin.cases b (fun _ => a)), fun _ => a⟩ :
      Env (smdl_structure_l I (R := S) ⟨H, layer.member⟩) 3)
    (Fin.cases hF (Fin.cases hB (fun _ => hA)))
  exact (rd_entry0_sat_l hZF.1 ..).symm.trans (read.trans (rd_entry0_sat_l ext ..))

theorem Rr_layer_d.low_composition_l {Γ Y S H k D E A Q F G : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d e a q f g : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hD : Rd_entry_d D d.val k) (hE : Rd_entry_d E e.val k) (hA : Rd_entry_d A a.val k)
    (hQ : Rd_entry_d Q q.val k) (hF : Rd_entry_d F f.val k) (hG : Rd_entry_d G g.val k) :
    Cp0_d D E A Q F G ↔ Cp0_d d e a q f g := by
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨D, layer.injection.1.input_mem_of_pairMember hD⟩⟩
  have read := rr_realize_delta_l I layer.transitive nx ⟨H, layer.member⟩ layer.injection layer.predecessors
    (cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (cp0_delta_l ..)
    (⟨Fin.cases ⟨G, layer.injection.1.input_mem_of_pairMember hG⟩
      (Fin.cases ⟨F, layer.injection.1.input_mem_of_pairMember hF⟩
      (Fin.cases ⟨Q, layer.injection.1.input_mem_of_pairMember hQ⟩
      (Fin.cases ⟨A, layer.injection.1.input_mem_of_pairMember hA⟩
      (Fin.cases ⟨E, layer.injection.1.input_mem_of_pairMember hE⟩
        (fun _ => ⟨D, layer.injection.1.input_mem_of_pairMember hD⟩))))),
      fun _ => ⟨D, layer.injection.1.input_mem_of_pairMember hD⟩⟩ : Env (rt_model_l Γ nx) 6)
    (⟨Fin.cases g (Fin.cases f (Fin.cases q (Fin.cases a (Fin.cases e (fun _ => d))))),
      fun _ => d⟩ : Env (smdl_structure_l I (R := S) ⟨H, layer.member⟩) 6)
    (Fin.cases hG (Fin.cases hF (Fin.cases hQ (Fin.cases hA (Fin.cases hE (fun _ => hD))))))
  exact (cp0_sat_l hZF.1 ..).symm.trans (read.trans (cp0_sat_l ext ..))

/-- 高值域以原对象码读取；两个定义域的完整前驱保证反向也覆盖全部内部坐标。 -/
theorem Rr_layer_d.composition_l {Γ Y S H k D E A Q F G : M.Domain}
    (layer : Rr_layer_d I Γ Y S H k)
    (ext : Extensional (smdl_structure_l I (R := S) ⟨H, layer.member⟩))
    (d e a q f g : (smdl_structure_l I (R := S) ⟨H, layer.member⟩).Domain)
    (hD : Rd_entry_d D d.val k) (hE : Rd_entry_d E e.val k) (hQ : Rd_entry_d Q q.val k)
    (carrier : ∀ x, M.mem x A ↔ M.mem x Y ∧ Rd_entry_d x a.val S)
    (fg : Fn0_d D A G) (ng : Fn0_d d a g)
    (gf : Rc_graph_d I Y S k f.val F) (gg : Rc_graph_d I Y S k g.val G) :
    Cp0_d D E A Q F G ↔ Cp0_d d e a q f g := by
  let N := smdl_structure_l I (R := S) ⟨H, layer.member⟩
  constructor
  · intro comp
    refine ⟨ng, fun i hi => ?_⟩
    obtain ⟨s, hs, hsi⟩ := (layer.predecessors D d.val hD i.val).mp hi
    obtain ⟨r, hr, x, hx, hsr, hrx, hsx⟩ := comp.2 s hs
    obtain ⟨j, hj, hrj⟩ := layer.injection.1.2.2 r
      (layer.transitive E (layer.injection.1.input_mem_of_pairMember hE) r hr)
    let j' : N.Domain := ⟨j, hj⟩
    let x' : N.Domain := ⟨x, ((carrier x).mp hx).1⟩
    exact ⟨j', (layer.predecessors E e.val hE j).mpr ⟨r, hr, hrj⟩,
      x', ((carrier x).mp hx).2, (layer.entry_l hZF ext i j' q hsi hrj hQ).mp hsr,
      (rf_val_native_l I _ ext j' x' f).mp ((gf r j x hrj).mp hrx),
      (rf_val_native_l I _ ext i x' g).mp ((gg s i.val x hsi).mp hsx)⟩
  · intro comp
    refine ⟨fg, fun s hs => ?_⟩
    obtain ⟨i, hi, hsi⟩ := layer.injection.1.2.2 s
      (layer.transitive D (layer.injection.1.input_mem_of_pairMember hD) s hs)
    let i' : N.Domain := ⟨i, hi⟩
    obtain ⟨j, hj, x, hx, hij, hjx, hix⟩ := comp.2 i'
      ((layer.predecessors D d.val hD i).mpr ⟨s, hs, hsi⟩)
    obtain ⟨r, hr, hrj⟩ := (layer.predecessors E e.val hE j.val).mp hj
    exact ⟨r, hr, x.val, (carrier x.val).mpr ⟨x.property, hx⟩,
      (layer.entry_l hZF ext i' j q hsi hrj hQ).mpr hij,
      (gf r j.val x.val hrj).mpr ((rf_val_native_l I _ ext j x f).mpr hjx),
      (gg s i x.val hsi).mpr ((rf_val_native_l I _ ext i' x g).mpr hix)⟩

end YesMetaZFC.SetTheory.Internal
