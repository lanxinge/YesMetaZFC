import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Relations.CrossMeasure
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationSuccessor
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyClass

/-! # 原关系共同切片上的实际下一分量与完整 Łoś

所属模型内部构造有限幂和同一扩展器测度，背景只读取它们的对象码。
两侧切片识别全部坐标子集族，原测度便直接作用于当前源的全部真值集。
商、常值图、原地模型的复合图及完整内部 ZFC 保持均由同一次构造返回。
所属模型只需 KP 及实际有限 κ 幂的幂集；不要求其余对象的幂集或完整 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_reduced_l {ω c X R c' Y S q Γ H k N T z L n a : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d I X R) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (small : Rr_small_d I Y S H)
    (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (hn : M.mem n ω) (support : Fn0_d n L a)
    (loc : It_local_d I w.val N T ξ.val ℓ.val f.val) :
    ∃ m b d u : (smdl_structure_l I (R := T) nx).Domain,
      Rd_entry_d n m.val z ∧ Rf_fun_d I N T m.val b.val ∧ Rc_graph_d I N T z b.val a ∧
      Fn0_d m ℓ b ∧ Ep_space_d ξ m d ∧ (smdl_structure_l I (R := T) nx).mem d U ∧ Rd_entry_d b u f ∧
      ∃ D t₀ t v P V G o r C W j q',
        (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) ∧
        M.IsSetFunctionFromTo I t₀ D N ∧ (∀ x y, Rd_entry_d x y t₀ ↔ M.mem x D ∧ x = y) ∧
        M.IsRestrictionOf I t k D ∧ Fn0_d D Y t ∧ Rd_entry_d d.val v k ∧
        (∀ s x, Rd_entry_d s x t → Rd_entry_d x v S) ∧
        Rt_source_d I N T D t₀ P ∧ Rt_source_d I Y S D t P ∧ Rel_ultra_d D P V ∧
        (∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d I D t₀ T B A) ∧
        Rc_family_d I Y S D v t G ∧ Rp_model_d I D Y V S o G r C W ∧
        Smap_d I ω c' o Y C j ∧ Smap_d I ω c o X C q' ∧
        (Zc_model_d I ω c X R → Zc_model_d I ω o C W) ∧
        (∀ x E, Rd_entry_d x E q' ↔ M.mem x X ∧ ∃ y, Rd_entry_d x y q ∧ Rd_entry_d y E j) ∧
        (∀ x B, Rd_entry_d x B j ↔ M.mem x Y ∧ ∃ g, M.mem g G ∧ Rs_const_d D x g ∧ Rd_entry_d g B r) ∧
        (∀ x B E, Rd_entry_d x B j → Rd_entry_d E B W →
          ∃ g, M.mem g G ∧ Rd_entry_d g E r ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y x S) ∧
        ∀ E Z α t' q₀, M.IsFunctionSpace I E ω Y → Scode_d I ω Z →
          M.mem α E → M.IsSetFunctionFromTo I t' ω C → Rc_eval_d I ω v Y S t r α t' → M.mem q₀ Z →
          (Satisfies_d I ω o q₀ t' ↔ ∃ A, M.mem A V ∧ ∀ s x, M.mem s A → Rd_entry_d s x t →
            ∃ g, M.mem g E ∧ Pe_assign_d I ω v Y S α g x ∧ Satisfies_d I ω c' q₀ g) := by
  let N₀ := smdl_structure_l I (R := T) nx
  obtain ⟨m₀, b₀, hm, fn, graph⟩ := numbers.finite_function_l hZF hN.1 (KP.exists_pair hN) (KP.exists_union hN) hω
    (fun _ h => h) hn (support.mono_target_l (fun x hx => ((length x).mp hx).1))
  let m : N₀.Domain := ⟨m₀, numbers.injection.1.output_mem_of_pairMember hm⟩
  let b : N₀.Domain := ⟨b₀, fn.mem_l I⟩
  have support' := numbers.function_range_l hZF hN.1 m ℓ b hm support
    (fun x hx => ((length x).mp hx).2) fn graph
  have hn' : N₀.mem m w := (numbers.image m.val).mpr ⟨n, hn, hm⟩
  obtain ⟨d, hd, space⟩ := finite.spaces ξ m hξ hn'
  have actual := loc.read_l I _ (kp_pair_l hN) hN.1 w ξ ℓ f
  obtain ⟨u, hbu⟩ := actual.measures.total m b hn' support'
  have measure := actual.measures.at_l hN.1 hbu support' space
  -- 同一个原测度读成当前源的完整相对超滤，子集族在两侧逐项相同。
  obtain ⟨D, t₀, t, v, P, V, dc, ft₀, id, rt, ft, hdv, hvH, domain, _, ownerP, targetP, ultra, spec⟩ :=
    rr_cross_measure_l hZF hω mx theory model hq nx hN U d u finite.transitive carrier ownerClosed
      fk image pred closed hd (powers m d hn' space) measure
  have hv := fk.1.output_mem_of_pairMember hdv
  have ft := fn0_of_function_l (ZF.modelsKP hZF) ft
  have same A : M.mem A V ↔ M.mem A P ∧ M.mem A V :=
    ⟨fun h => ⟨ultra.admissible A h, h⟩, And.right⟩
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω mx model ex
  have collect := (sc_collection_iff_l I hZF hω mx model
    (ex.native_l I mx.2.1) (ext.native_l I model.2.1) hq).mp collection
  obtain ⟨G, o, r, C, W, j, q', quotient, _, functions, embed, composite, square, constants, bounded, los⟩ :=
    rc_successor_l hZF hω ex mx theory model hq ⟨v, hv⟩ (collect.uniform_l I (small v hv hvH)) ft domain targetP
      ultra.base ultra.proper ultra.upward ultra same
  have family := (rc_family_native_l I model.2.1 (ext.native_l I model.2.1) ⟨v, hv⟩ ft).mpr functions
  exact ⟨m, b, d, u, hm, fn, graph, support', space, hd, hbu,
    D, t₀, t, v, P, V, G, o, r, C, W, j, q', dc, ft₀, id, rt, ft, hdv, domain, ownerP, targetP,
    ultra, spec, family, quotient, embed, composite, (fun certificate => certificate.map_l hZF hω quotient.code composite),
    square, constants, bounded, los⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系中的有限幂对象

有限幂按原公式读取，背景只保存其对象码；解释不要求所属模型传递。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_space_d (N T ξ m d : M.Domain) : Prop :=
  Rr_truth_d I (n := 2) N T (ep_space_m (.bound 2) (.bound 1) .newest)
    (Fin.cases d (Fin.cases m (fun _ => ξ)))

def er_space_m {n} (N T ξ m d : Term n) : Formula 1 n :=
  rr_truth_m (𝒞 := kpair_convention_l) (n := 2) (ep_space_m (.bound 2) (.bound 1) .newest) N T
    (Fin.cases d (Fin.cases m (fun _ => ξ)))

@[simp] theorem er_space_closed_l {n} (N T ξ m d : Term n)
    (hN : N.freeSupport = []) (hT : T.freeSupport = []) (hξ : ξ.freeSupport = [])
    (hm : m.freeSupport = []) (hd : d.freeSupport = []) : (er_space_m N T ξ m d).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hN hT (Fin.cases hd (Fin.cases hm (fun _ => hξ)))

theorem er_space_sat_l {n} (ρ : Env M n) (N T ξ m d : Term n) :
    Formula.satisfies ρ (er_space_m N T ξ m d) ↔ Er_space_d I (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (m.eval ρ) (d.eval ρ) := by
  unfold er_space_m
  rw [rr_truth_sat_l I _ _ (by simp -implicitDefEqProofs)]
  have row : (fun i : Fin 3 => ((Fin.cases d (Fin.cases m (fun _ => ξ)) : Fin 3 → Term n) i).eval ρ) =
      Fin.cases (d.eval ρ) (Fin.cases (m.eval ρ) (fun _ => ξ.eval ρ)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  rw [row]
  rfl

theorem er_space_native_l {N T : M.Domain} (nx : ∃ x, M.mem x N)
    (ext : Extensional (smdl_structure_l I (R := T) nx))
    (ξ m d : (smdl_structure_l I (R := T) nx).Domain) :
    Er_space_d I N T ξ.val m.val d.val ↔ Ep_space_d ξ m d := by
  rcases ξ with ⟨ξ, hξ⟩
  rcases m with ⟨m, hm⟩
  rcases d with ⟨d, hd⟩
  let v : Fin 3 → M.Domain := Fin.cases d (Fin.cases m (fun _ => ξ))
  have hv : ∀ i, M.mem (v i) N := Fin.cases hd (Fin.cases hm (fun _ => hξ))
  let ρ : Env (smdl_structure_l I (R := T) nx) 3 :=
    ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨d, hd⟩⟩
  constructor
  · rintro ⟨_, valid⟩
    exact (ep_space_sat_l ext ρ (.bound 2) (.bound 1) .newest).mp valid
  · intro h
    exact ⟨hv, (ep_space_sat_l ext ρ (.bound 2) (.bound 1) .newest).mpr h⟩

/-- 两端由同一有限幂公式确定的对象，必是给定原初等图下的实际像。 -/
theorem Er_space_d.image_unique_l (hZF : M.Models ZF)
    {ω c N T c' N' T' σ ξ m d ξ' m' d' : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c N T) (my : Smdl_d I c' N' T')
    (map : Smap_d I ω c c' N N' σ)
    (ext : Extensional (smdl_structure_l I (R := T') my.2.1))
    (hξ : M.PairMember I ξ ξ' σ) (hm : M.PairMember I m m' σ)
    (source : Er_space_d I N T ξ m d) (target : Er_space_d I N' T' ξ' m' d') :
    M.PairMember I d d' σ := by
  obtain ⟨D, hD, hdD⟩ := map.1.1.2.2 d (source.elim fun h _ => h 0)
  have moved : Er_space_d I N' T' ξ' m' D := Rr_truth_d.map_l I hZF hω mx my map
    (by simp -implicitDefEqProofs) source (Fin.cases hdD (Fin.cases hm (fun _ => hξ)))
  let ξ₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨ξ', map.1.1.output_mem_of_pairMember hξ⟩
  let m₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨m', map.1.1.output_mem_of_pairMember hm⟩
  let d₁ : (smdl_structure_l I (R := T') my.2.1).Domain := ⟨d', target.elim fun h _ => h 0⟩
  have ds := (er_space_native_l I my.2.1 ext ξ₁ m₁ ⟨D, hD⟩).mp moved
  have ds' := (er_space_native_l I my.2.1 ext ξ₁ m₁ d₁).mp target
  have eq : D = d' := congrArg Subtype.val (ext.eq_of_same_members ⟨D, hD⟩ d₁
    (fun x => (ds x).trans (ds' x).symm))
  exact eq ▸ hdD

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原关系有限幂的实际子集一致性

共同图只须覆盖临界点、有限 κ 幂及其两侧子集。完整前驱保证该图保持并
反映子集关系；共同秩段通过已实现的有限闭包自动给出此较弱证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Er_agree_d (ω X R κ z Γ Y S k : M.Domain) : Prop where
  domain : M.MemberSubset Γ X
  downward : ∀ x y, M.mem x Γ → M.mem y X → M.PairMember I y x R → M.mem y Γ
  injection : M.IsSetInjectionFromTo I k Γ Y
  predecessors : ∀ x y, M.PairMember I x y k → ∀ v,
    M.PairMember I v y S ↔ ∃ s, M.PairMember I s x R ∧ M.PairMember I s v k
  critical : M.mem κ Γ
  powers : ∀ n m d, M.mem n ω → M.PairMember I n m z → Er_space_d I X R κ m d →
    ∃ e, M.PairMember I d e k ∧
      (∀ A, M.mem A X → (∀ x, M.mem x X → M.PairMember I x A R → M.PairMember I x d R) → M.mem A Γ) ∧
      ∀ B, M.mem B Y → (∀ y, M.mem y Y → M.PairMember I y B S → M.PairMember I y e S) →
        ∃ A, M.PairMember I A B k

def er_agree_m {d} (ω X R κ z Γ Y S k : Term d) : Formula 1 d := set[d] ⟪
  ⌜Γ⌝ₛ ⊆ ⌜X⌝ₛ ∧
  (∀ x y, x ∈ ⌜Γ⌝ₛ → y ∈ ⌜X⌝ₛ → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, x, ⌜R⌝ₛ) → y ∈ ⌜Γ⌝ₛ) ∧
  ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜k⌝ₛ, ⌜Γ⌝ₛ, ⌜Y⌝ₛ) ∧
  (∀ x y, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, y, ⌜k⌝ₛ) → ∀ v, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(v, y, ⌜S⌝ₛ) ↔
    (∃ s, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(s, x, ⌜R⌝ₛ) ∧ ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(s, v, ⌜k⌝ₛ))) ∧
  ⌜κ⌝ₛ ∈ ⌜Γ⌝ₛ ∧
  (∀ n m d, n ∈ ⌜ω⌝ₛ → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(n, m, ⌜z⌝ₛ) →
    ⌜er_space_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜κ⌝ₛ, m, d) → ∃ e, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(d, e, ⌜k⌝ₛ) ∧
      (∀ A, A ∈ ⌜X⌝ₛ → (∀ x ∈ ⌜X⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, A, ⌜R⌝ₛ) → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, d, ⌜R⌝ₛ)) → A ∈ ⌜Γ⌝ₛ) ∧
      (∀ B, B ∈ ⌜Y⌝ₛ → (∀ y ∈ ⌜Y⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, B, ⌜S⌝ₛ) → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, e, ⌜S⌝ₛ)) →
        ∃ A, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(A, B, ⌜k⌝ₛ)))⟫
derive_free_closed er_agree_m

theorem er_agree_sat_l (ext : Extensional M) {d} (ρ : Env M d) (ω X R κ z Γ Y S k : Term d) :
    Formula.satisfies ρ (er_agree_m ω X R κ z Γ Y S k) ↔
      Er_agree_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (κ.eval ρ) (z.eval ρ)
        (Γ.eval ρ) (Y.eval ρ) (S.eval ρ) (k.eval ρ) := by
  simp only [er_agree_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isInjectionFromTo_iff I ext,
    er_space_sat_l I, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
    fun h => ⟨h.domain, h.downward, h.injection, h.predecessors, h.critical, h.powers⟩⟩

/-- 现有共同秩段自动提供每个内部有限幂的全部子集对应。 -/
theorem er_agree_layer_l {ω X R z Γ Y S H k : M.Domain} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (w U κ : (smdl_structure_l I (R := R) nx).Domain)
    (numbers : Rr_layer_d I ω X R w.val z) (finite : Fs_read_d w U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x X ∧ M.PairMember I x U.val R)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, M.PairMember I y H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x y k)
    (pred : ∀ x y, M.PairMember I x y k → ∀ v, M.PairMember I v y S ↔ ∃ s, M.PairMember I s x R ∧ M.PairMember I s v k)
    (ownerClosed : Rr_closed_d I X R U.val) (parentClosed : Rr_closed_d I Y S H)
    (hκ : (smdl_structure_l I (R := R) nx).mem κ U) : Er_agree_d I ω X R κ.val z Γ Y S k := by
  let N := smdl_structure_l I (R := R) nx
  refine ⟨fun x hx => ((carrier x).mp hx).1, ?_, fk, pred, (carrier κ.val).mpr ⟨κ.property, hκ⟩, ?_⟩
  · intro x y hx hy hyx
    exact (carrier y).mpr ⟨hy, finite.transitive ⟨x, ((carrier x).mp hx).1⟩ ((carrier x).mp hx).2 ⟨y, hy⟩ hyx⟩
  · intro n m d hn hnm space
    let m₀ : N.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
    let d₀ : N.Domain := ⟨d, space.elim fun h _ => h 0⟩
    have hm : N.mem m₀ w := (numbers.image m).mpr ⟨n, hn, hnm⟩
    have full := (er_space_native_l I nx ext κ m₀ d₀).mp space
    obtain ⟨D, hD, ds⟩ := finite.spaces κ m₀ hκ hm
    have eq := ext.eq_of_same_members D d₀ (fun x => (ds x).trans (full x).symm)
    have hd : N.mem d₀ U := eq ▸ hD
    obtain ⟨e, he, hde⟩ := fk.1.2.2 d ((carrier d).mpr ⟨d₀.property, hd⟩)
    refine ⟨e, hde, fun A hA sub => (carrier A).mpr ⟨hA, ownerClosed d A d₀.property hA hd sub⟩, ?_⟩
    intro B hB sub
    obtain ⟨A, _, hAB⟩ := (image B).mp
      (parentClosed e B he hB ((image e).mpr ⟨d, fk.1.input_mem_of_pairMember hde, hde⟩) sub)
    exact ⟨A, hAB⟩

/-- 后继中的任意子集都对应原有限幂的同一个原关系子集。 -/
theorem Er_agree_d.subsets_l {ω X R κ z Γ Y S k n m d : M.Domain}
    (h : Er_agree_d I ω X R κ z Γ Y S k) (hn : M.mem n ω)
    (hnm : M.PairMember I n m z) (space : Er_space_d I X R κ m d) :
    ∃ e, M.PairMember I d e k ∧
      ∀ B, M.mem B Y → ((∀ y, M.mem y Y → M.PairMember I y B S → M.PairMember I y e S) ↔
        ∃ A, M.mem A X ∧ (∀ x, M.mem x X → M.PairMember I x A R → M.PairMember I x d R) ∧ M.PairMember I A B k) := by
  obtain ⟨e, hde, _, back⟩ := h.powers n m d hn hnm space
  refine ⟨e, hde, fun B hB => ⟨?_, ?_⟩⟩
  · intro sub
    obtain ⟨A, hAB⟩ := back B hB sub
    have hA := h.injection.1.input_mem_of_pairMember hAB
    refine ⟨A, h.domain A hA, ?_, hAB⟩
    intro x hx hxA
    obtain ⟨y, hy, hxy⟩ := h.injection.1.2.2 x (h.downward A x hA hx hxA)
    obtain ⟨x', hx'd, hx'y⟩ := (h.predecessors d e hde y).mp
      (sub y hy ((h.predecessors A B hAB y).mpr ⟨x, hxA, hxy⟩))
    exact h.injection.2 x' x y hx'y hxy ▸ hx'd
  · rintro ⟨A, _, sub, hAB⟩ y _ hyB
    obtain ⟨x, hxA, hxy⟩ := (h.predecessors A B hAB y).mp hyB
    exact (h.predecessors d e hde y).mpr
      ⟨x, sub x (h.domain x (h.injection.1.input_mem_of_pairMember hxy)) hxA, hxy⟩

/-- 两侧实际子集族相同，原测度直接成为父模型真值族上的相对超滤。 -/
theorem Er_agree_d.measure_l (hZF : M.Models ZF)
    {ω c N T Γ Y S k z n D i t y V : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c Y S) (theory : Sc_theory_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (ξ m d u : (smdl_structure_l I (R := T) nx).Domain)
    (h : Er_agree_d I ω N T ξ.val z Γ Y S k)
    (hn : M.mem n ω) (hnm : M.PairMember I n m.val z) (space : Er_space_d I N T ξ.val m.val d.val)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ M.PairMember I x d.val T)
    (fi : M.IsSetFunctionFromTo I i D N)
    (id : ∀ x v, M.PairMember I x v i ↔ M.mem x D ∧ x = v)
    (rt : M.IsRestrictionOf I t k D) (hdy : M.PairMember I d.val y k)
    (power : ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d) (measure : FilterZF.Maximal_d d u)
    (spec : ∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ M.PairMember I B u.val T ∧ Rt_trace_d I D i T B A) :
    ∃ P, M.IsSetFunctionFromTo I t D Y ∧ Rt_source_d I N T D i P ∧
      Rt_source_d I Y S D t P ∧ FilterZF.Rel_ultra_d D P V := by
  have dom s x (hsx : M.PairMember I s x i) := ((id s x).mp hsx).2 ▸ ((dc s).mp ((id s x).mp hsx).1).2
  have onto x (hx : M.mem x N) (hxd : M.PairMember I x d.val T) : ∃ s, M.mem s D ∧ M.PairMember I s x i := by
    have hs := (dc x).mpr ⟨hx, hxd⟩
    exact ⟨x, hs, (id x x).mpr ⟨hs, rfl⟩⟩
  have ft := rt.isSetFunctionFromTo h.injection.1 (fun x hx => h.downward d.val x
    (h.injection.1.input_mem_of_pairMember hdy) ((dc x).mp hx).1 ((dc x).mp hx).2)
  have dom' s x (hsx : M.PairMember I s x t) := (h.predecessors d.val y hdy x).mpr
    ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  obtain ⟨y₀, hdy₀, front, back⟩ := h.powers n m.val d.val hn hnm space
  have eq := h.injection.1.1.2 d.val y₀ y hdy₀ hdy
  subst y₀
  obtain ⟨P, source⟩ := rt_source_exists_l I hZF N T D i
  have target : Rt_source_d I Y S D t P := by
    intro A
    constructor
    · intro hA
      obtain ⟨B, hB, trace⟩ := (source A).mp hA
      obtain ⟨a, cut⟩ := KP.intersection_exists_d hN d ⟨B, hB⟩
      obtain ⟨a', ha', haa⟩ := h.injection.1.2.2 a.val
        (front a.val a.property (fun x hx hxa => ((cut ⟨x, hx⟩).mp hxa).1))
      refine ⟨a', ha', (rr_trace_transport_l I h.injection h.predecessors ft id rt haa).mp ?_⟩
      exact fun s => (trace s).trans (and_congr_right fun _ => exists_congr fun x => and_congr_right fun hsx =>
        ((cut ⟨x, fi.output_mem_of_pairMember hsx⟩).trans (and_iff_right (dom s x hsx))).symm)
    · rintro ⟨B, hB, trace⟩
      obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c) hω
      obtain ⟨a', ha', cut⟩ := sc_cut_raw_l I hZF hω model theory model identity true
        (h.injection.1.output_mem_of_pairMember hdy) hB
      obtain ⟨a, haa⟩ := back a' ha' (fun x hx hxa => ((cut x hx).mp hxa).1)
      refine (source A).mpr ⟨a, h.domain a (h.injection.1.input_mem_of_pairMember haa),
        (rr_trace_transport_l I h.injection h.predecessors ft id rt haa).mpr ?_⟩
      exact fun s => (trace s).trans (and_congr_right fun _ => exists_congr fun x => and_congr_right fun hsx =>
        ((cut x (ft.output_mem_of_pairMember hsx)).trans (and_iff_right (dom' s x hsx))).symm)
  exact ⟨P, ft, source, target, rt_ultra_l I hZF nx hN d u fi dom onto power source measure spec⟩

/-- 已实现的共同小层给出所需有限幂定义域的大小界。 -/
theorem er_domain_small_l {ω N T ξ z Γ Y S H k : M.Domain}
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, M.PairMember I y H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x y k)
    (small : Rr_small_d I Y S H) :
    ∀ n m d y, M.mem n ω → M.PairMember I n m z → Er_space_d I N T ξ m d →
      M.PairMember I d y k → Rf_small_d I Y S y :=
  fun _ _ d y _ _ _ hdy => small y (fk.1.output_mem_of_pairMember hdy)
    ((image y).mpr ⟨d, fk.1.input_mem_of_pairMember hdy, hdy⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 对象码分量的规范定义

支撑、有限幂、原测度、坐标迹和代表族均由固定公式读取。规范结构码
只由这些实际对象决定，因而可对全部内部有限支撑一次使用替换。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 指定分量数据的原证书，保留支撑、坐标图与同一商之间的精确联系。 -/
def Er_frame_d (ω L N T ξ F z Y S k a c n m b d u D i t y V G p C W : M.Domain) : Prop :=
    M.mem n ω ∧ Fn0_d n L a ∧ Rd_entry_d n m z ∧ Rf_fun_d I N T m b ∧ Rc_graph_d I N T z b a ∧
    Er_space_d I N T ξ m d ∧ Rf_val_d I N T b u F ∧
    (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d T) ∧
    Fn0_d D N i ∧ (∀ x y, Rd_entry_d x y i ↔ M.mem x D ∧ x = y) ∧
    M.IsRestrictionOf I t k D ∧ Rd_entry_d d y k ∧
    (∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u T ∧ Rt_trace_d I D i T B A) ∧
    Rc_family_d I Y S D y t G ∧ Rp_model_d I D Y V S c G p C W

def Er_code_d (ω L N T ξ F z Y S k a c : M.Domain) : Prop :=
  ∃ n m b d u D i t y V G p C W, Er_frame_d I ω L N T ξ F z Y S k a c n m b d u D i t y V G p C W

def er_frame_m {v} (ω L N T ξ F z Y S k a c n m b d u D i t y V G p C W : Term v) : Formula 1 v := set[v] ⟪
  ⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜n⌝ₛ, ⌜L⌝ₛ, ⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜n⌝ₛ, ⌜m⌝ₛ, ⌜z⌝ₛ) ∧
  ⌜rf_fun_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜m⌝ₛ, ⌜b⌝ₛ) ∧
  ⌜rc_graph_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜z⌝ₛ, ⌜b⌝ₛ, ⌜a⌝ₛ) ∧
  ⌜er_space_m⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜m⌝ₛ, ⌜d⌝ₛ) ∧
  ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜b⌝ₛ, ⌜u⌝ₛ, ⌜F⌝ₛ) ∧
  (∀ x, x ∈ ⌜D⌝ₛ ↔ x ∈ ⌜N⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x, ⌜d⌝ₛ, ⌜T⌝ₛ)) ∧
  ⌜fn0_m⌝ₚ(⌜D⌝ₛ, ⌜N⌝ₛ, ⌜i⌝ₛ) ∧ (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜i⌝ₛ) ↔ x ∈ ⌜D⌝ₛ ∧ x = y) ∧
  ⌜Formula.isRestriction kpair_convention_l⌝ₚ(⌜t⌝ₛ, ⌜k⌝ₛ, ⌜D⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜d⌝ₛ, ⌜y⌝ₛ, ⌜k⌝ₛ) ∧
  (∀ A, A ∈ ⌜V⌝ₛ ↔ (∃ B ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(B, ⌜u⌝ₛ, ⌜T⌝ₛ) ∧
    ⌜rt_trace_m (𝒞 := kpair_convention_l)⌝ₚ(⌜D⌝ₛ, ⌜i⌝ₛ, ⌜T⌝ₛ, B, A))) ∧
  ⌜rc_family_m⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜D⌝ₛ, ⌜y⌝ₛ, ⌜t⌝ₛ, ⌜G⌝ₛ) ∧
  ⌜rp_model_m (𝒞 := kpair_convention_l)⌝ₚ(⌜D⌝ₛ, ⌜Y⌝ₛ, ⌜V⌝ₛ, ⌜S⌝ₛ, ⌜c⌝ₛ, ⌜G⌝ₛ, ⌜p⌝ₛ, ⌜C⌝ₛ, ⌜W⌝ₛ)⟫

derive_free_closed er_frame_m

theorem er_frame_sat_l (hE : Extensional M) {v} (ρ : Env M v)
    (ω L N T ξ F z Y S k a c n m b d u D i t y V G p C W : Term v) :
    Formula.satisfies ρ (er_frame_m ω L N T ξ F z Y S k a c n m b d u D i t y V G p C W) ↔
      Er_frame_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (F.eval ρ) (z.eval ρ)
        (Y.eval ρ) (S.eval ρ) (k.eval ρ) (a.eval ρ) (c.eval ρ) (n.eval ρ) (m.eval ρ) (b.eval ρ) (d.eval ρ)
        (u.eval ρ) (D.eval ρ) (i.eval ρ) (t.eval ρ) (y.eval ρ) (V.eval ρ) (G.eval ρ) (p.eval ρ) (C.eval ρ) (W.eval ρ) := by
  simp only [er_frame_m, Er_frame_d, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, rd_entry0_sat_l hE, rf_fun_sat_l I, rc_graph_sat_l I hE,
    er_space_sat_l I, rf_val_sat_l I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_existsMem_iff, rt_trace_sat_l I, rc_family_sat_l I hE, rp_model_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

def er_code_m {n} (ω L N T ξ F z Y S k a c : Term n) : Formula 1 n := set[n] ⟪
  ∃ n m b d u D i t y V G p C W, ⌜er_frame_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜F⌝ₛ,
    ⌜z⌝ₛ, ⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜k⌝ₛ, ⌜a⌝ₛ, ⌜c⌝ₛ, n, m, b, d, u, D, i, t, y, V, G, p, C, W)⟫

derive_free_closed er_code_m

theorem er_code_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω L N T ξ F z Y S k a c : Term n) :
    Formula.satisfies ρ (er_code_m ω L N T ξ F z Y S k a c) ↔
      Er_code_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (F.eval ρ) (z.eval ρ)
        (Y.eval ρ) (S.eval ρ) (k.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [er_code_m, Er_code_d, Formula.satisfies_exists_iff, er_frame_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

section Construction
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_frame_d.unique_l {ω L N T w z Y S k a c c' n m b d u D i t y V G p C W
    n' m' b' d' u' D' i' t' y' V' G' p' C' W' : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ξ f : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (function : ∀ b u v, Rd_entry_d b u f → Rd_entry_d b v f → u = v)
    (fk : M.IsSetFunction Kp k)
    (h : Er_frame_d Kp ω L N T ξ.val f.val z Y S k a c n m b d u D i t y V G p C W)
    (h' : Er_frame_d Kp ω L N T ξ.val f.val z Y S k a c' n' m' b' d' u' D' i' t' y' V' G' p' C' W') :
    c = c' ∧ n = n' ∧ m = m' ∧ b = b' ∧ d = d' ∧ u = u' ∧ D = D' ∧ i = i' ∧
      t = t' ∧ y = y' ∧ V = V' ∧ G = G' ∧ p = p' ∧ C = C' ∧ W = W' := by
  let N₀ := smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩
  obtain ⟨hn, fa, hnm, fn, ga, space, value, dc, fi, id, rt, hdy, measure, family, model⟩ := h
  obtain ⟨hn', fa', hnm', fn', ga', space', value', dc', fi', id', rt', hdy', measure', family', model'⟩ := h'
  have eq := fa'.domain_eq_l hZF.1 fa
  subst n'
  have eq := numbers.injection.1.1.2 n m' m hnm' hnm
  subst m'
  have eq := (show Rr_finite_d Kp ω L N T z a b' from ⟨n, m, hn', fa', hnm', fn', ga'⟩).unique_l
    hZF numbers ext ⟨n, m, hn, fa, hnm, fn, ga⟩
  subst b'
  let m₀ : N₀.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let d₀ : N₀.Domain := ⟨d, space.elim (fun h _ => h 0)⟩
  let d₁ : N₀.Domain := ⟨d', space'.elim (fun h _ => h 0)⟩
  have ds := (er_space_native_l Kp _ ext ξ m₀ d₀).mp space
  have ds' := (er_space_native_l Kp _ ext ξ m₀ d₁).mp space'
  have eq : d' = d := congrArg (fun x : N₀.Domain => x.val)
    (ext.eq_of_same_members d₁ d₀ (fun x => (ds' x).trans (ds x).symm))
  subst d'
  have eq : u' = u := congrArg (fun x : N₀.Domain => x.val)
    (function ⟨b, fn.mem_l Kp⟩ ⟨u', (value'.bounds_l Kp).2.1⟩ ⟨u, (value.bounds_l Kp).2.1⟩
      ((rf_val_native_l Kp _ ext ..).mp value') ((rf_val_native_l Kp _ ext ..).mp value))
  subst u'
  have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
  subst D'
  have eq := (fn0_function_l (ZF.modelsKP hZF) fi').1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) fi).1.1 (fun x y => (id' x y).trans (id x y).symm)
  subst i'
  have eq := rt'.1.eq_of_pairMember_iff hZF.1 rt.1 (fun x y => (rt'.2 x y).trans (rt.2 x y).symm)
  subst t'
  have eq := fk.2 d y' y hdy' hdy
  subst y'
  have eq := hZF.1.eq_of_same_members V' V (fun A => (measure' A).trans (measure A).symm)
  subst V'
  have eq := hZF.1.eq_of_same_members G' G (fun g => (family' g).trans (family g).symm)
  subst G'
  have hp := model.map.projection.1.1.eq_of_pairMember_iff hZF.1 model'.map.projection.1.1
    (fun g B => (model.map.classes g B).trans (model'.map.classes g B).symm)
  have hc := model.unique_l Kp hZF.1 model'
  subst c' p'
  obtain ⟨rfl, rfl⟩ := smdl_unique_l Kp model.code model'.code
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 同一支撑的实际分量证书唯一，因而其规范结构码唯一。 -/
theorem Er_code_d.unique_l {ω L N T w z Y S k a c c' : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ξ f : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (function : ∀ b u v, Rd_entry_d b u f → Rd_entry_d b v f → u = v)
    (fk : M.IsSetFunction Kp k)
    (h : Er_code_d Kp ω L N T ξ.val f.val z Y S k a c)
    (h' : Er_code_d Kp ω L N T ξ.val f.val z Y S k a c') : c = c' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, frame⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, frame'⟩ := h'
  exact (frame.unique_l hZF numbers ext ξ f function fk frame').1

/-- 原测度迹直接给出商的滤基；读取所属证书只需配对解释和外延性。 -/
theorem Er_code_d.base_l {ω L N T z Y S k a o : M.Domain}
    (nx : ∃ x, M.mem x N) (J : kpair_convention_l.Interpretation (smdl_structure_l Kp (R := T) nx))
    (ext : Extensional (smdl_structure_l Kp (R := T) nx))
    (w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val)
    (code : Er_code_d Kp ω L N T ξ.val f.val z Y S k a o) :
    ∃ D V G p C W, Rp_model_d Kp D Y V S o G p C W ∧ Base_d D V := by
  let N₀ := smdl_structure_l Kp (R := T) nx
  obtain ⟨n, m, b, d, u, D, i, t, y, V, G, p, C, W,
    hn, fa, hnm, fn, ga, space, value, dc, fi, id, _, _, measure, _, quotient⟩ := code
  let m₀ : N₀.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let b₀ : N₀.Domain := ⟨b, fn.mem_l Kp⟩
  let d₀ : N₀.Domain := ⟨d, space.elim (fun h _ => h 0)⟩
  let u₀ : N₀.Domain := ⟨u, (value.bounds_l Kp).2.1⟩
  have fb := numbers.function_range_l hZF ext m₀ ℓ b₀ hnm fa
    (fun x hx => ((length x).mp hx).2) fn ga
  have ds := (er_space_native_l Kp nx ext ξ m₀ d₀).mp space
  have hbu := (rf_val_native_l Kp nx ext b₀ u₀ f).mp value
  have actual := loc.read_l Kp nx J ext w ξ ℓ f
  have domain s x (hsx : Rd_entry_d s x i) : Rd_entry_d x d T := by
    obtain ⟨hs, rfl⟩ := (id s x).mp hsx
    exact ((dc s).mp hs).2
  exact ⟨D, V, G, p, C, W, quotient,
    rt_base_l Kp hZF nx d₀ u₀ (fn0_function_l (ZF.modelsKP hZF) fi) domain
      (actual.measures.at_l ext hbu fb ds).1.base_l measure⟩

/-- 从规范码恢复同一个原测度及两侧完整可测族，保留原商的全部对象。 -/
theorem Er_code_d.read_l {ω c X R c' Y S q Γ H k N T z L a o : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val)
    (code : Er_code_d Kp ω L N T ξ.val f.val z Y S k a o) :
    ∃ n, ∃ m b d u : (smdl_structure_l Kp (R := T) nx).Domain,
      M.mem n ω ∧ Fn0_d n L a ∧ Rd_entry_d n m.val z ∧ Rf_fun_d Kp N T m.val b.val ∧
      Rc_graph_d Kp N T z b.val a ∧ Fn0_d m ℓ b ∧ Ep_space_d ξ m d ∧
      (smdl_structure_l Kp (R := T) nx).mem d U ∧ Rd_entry_d b u f ∧
      ∃ D i t y P V G p C W,
        (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) ∧
        M.IsSetFunctionFromTo Kp i D N ∧ (∀ x y, Rd_entry_d x y i ↔ M.mem x D ∧ x = y) ∧
        M.IsRestrictionOf Kp t k D ∧ Fn0_d D Y t ∧ Rd_entry_d d.val y k ∧
        Rt_source_d Kp N T D i P ∧ Rt_source_d Kp Y S D t P ∧ Rel_ultra_d D P V ∧
        (∀ A, M.mem A V ↔ ∃ B, M.mem B N ∧ Rd_entry_d B u.val T ∧ Rt_trace_d Kp D i T B A) ∧
        Rc_family_d Kp Y S D y t G ∧ Rp_model_d Kp D Y V S o G p C W := by
  let N₀ := smdl_structure_l Kp (R := T) nx
  obtain ⟨n, m, b, d, u, D, i, t, y, V, G, p, C, W,
    hn, fa, hnm, fn, ga, space, value, dc, fi, id, rt, hdy, measure, family, quotient⟩ := code
  let m₀ : N₀.Domain := ⟨m, numbers.injection.1.output_mem_of_pairMember hnm⟩
  let b₀ : N₀.Domain := ⟨b, fn.mem_l Kp⟩
  let d₀ : N₀.Domain := ⟨d, space.elim (fun h _ => h 0)⟩
  let u₀ : N₀.Domain := ⟨u, (value.bounds_l Kp).2.1⟩
  have fb := numbers.function_range_l hZF hN.1 m₀ ℓ b₀ hnm fa
    (fun x hx => ((length x).mp hx).2) fn ga
  have ds := (er_space_native_l Kp nx hN.1 ξ m₀ d₀).mp space
  have hbu := (rf_val_native_l Kp nx hN.1 b₀ u₀ f).mp value
  have hm : N₀.mem m₀ w := (numbers.image m).mpr ⟨n, hn, hnm⟩
  obtain ⟨d', hd', ds'⟩ := finite.spaces ξ m₀ hξ hm
  have eq := hN.1.eq_of_same_members d' d₀ (fun x => (ds' x).trans (ds x).symm)
  have hd : N₀.mem d₀ U := eq ▸ hd'
  have actual := loc.read_l Kp _ (kp_pair_l hN) hN.1 w ξ ℓ f
  have agreement := er_agree_layer_l Kp nx hN.1 w U ξ numbers finite carrier fk image pred ownerClosed closed hξ
  have current := theory.map_l Kp hZF hω mx model hq
  obtain ⟨P, ft, source, target, ultra⟩ := agreement.measure_l Kp hZF hω model current nx hN ξ m₀ d₀ u₀
    hn hnm space dc (fn0_function_l (ZF.modelsKP hZF) fi) id rt hdy (powers m₀ d₀ hm ds)
    (actual.measures.at_l hN.1 hbu fb ds) measure
  exact ⟨n, m₀, b₀, d₀, u₀, hn, fa, hnm, fn, ga, fb, ds, hd, hbu,
    D, i, t, y, P, V, G, p, C, W, dc, fn0_function_l (ZF.modelsKP hZF) fi, id, rt,
    fn0_of_function_l (ZF.modelsKP hZF) ft, hdy, source, target, ultra, measure, family, quotient⟩


/-- 原分量码直接给出当前源的常值初等嵌入，所有代表仍来自原代表族。 -/
theorem Er_code_d.constant_l {ω c X R c' Y S q Γ H k N T z L a o : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val)
    (code : Er_code_d Kp ω L N T ξ.val f.val z Y S k a o) :
    ∃ C W j D, Smdl_d Kp o C W ∧ Smap_d Kp ω c' o Y C j ∧
      ∀ x B, Rd_entry_d x B j ↔ M.mem x Y ∧ M.mem B C ∧
        ∃ g, Fn0_d D Y g ∧ M.mem g B ∧ Rs_const_d D x g := by
  obtain ⟨_, _, _, d, _, _, _, _, _, _, _, _, hd, _,
    D, _, t, y, P, V, G, p, C, W, dc, _, _, rt, ft, hdy, _, source, ultra, _, family, quotient⟩ :=
    code.read_l hZF hω mx theory model hq nx hN U w ξ ℓ f numbers finite powers
      carrier ownerClosed fk image pred closed hξ length loc
  have hy := fk.1.output_mem_of_pairMember hdy
  let d' : (smdl_structure_l Kp (R := S) model.2.1).Domain := ⟨y, hy⟩
  have hyH := (image y).mpr ⟨d.val, (carrier d.val).mpr ⟨d.property, hd⟩, hdy⟩
  obtain ⟨μ, e, index⟩ := (small y hy hyH).index_l Kp model.2.1 d'
  have domain s x (hsx : Rd_entry_d s x t) : Rd_entry_d x y S :=
    (pred d.val y hdy x).mpr ⟨s, ((dc s).mp ((rt.2 s x).mp hsx).1).2, ((rt.2 s x).mp hsx).2⟩
  have ext : Rf_ext_d Kp Y S := hq.extensional_l hZF hω mx model ex
  have collect := (sc_collection_iff_l Kp hZF hω mx model
    (ex.native_l Kp mx.2.1) (ext.native_l Kp model.2.1) hq).mp collection
  have functions := (rc_family_native_l Kp model.2.1 (ext.native_l Kp model.2.1) d' ft).mp family
  obtain ⟨j, embed, constants⟩ := rc_constant_embedding_l hZF hω model ext (theory.map_l Kp hZF hω mx model hq)
    d' (collect model.2.1 d' μ e index) ft domain source ultra functions quotient
  refine ⟨C, W, j, D, quotient.code, embed, fun x B => ⟨?_, ?_⟩⟩
  · intro hxB
    obtain ⟨hx, g, hg, constant, gp⟩ := (constants x B).mp hxB
    exact ⟨hx, embed.1.1.output_mem_of_pairMember hxB, g, quotient.map.functions g hg,
      quotient.map.representative_l Kp ultra.base gp, constant⟩
  · rintro ⟨hx, hB, g, _, hg, constant⟩
    have gp := quotient.map.member_l Kp hZF.1 ultra.base hB hg
    exact (constants x B).mpr ⟨hx, g, quotient.map.projection.input_mem_of_pairMember gp, constant, gp⟩


/-- 全部不重复有限支撑共用规范模型表；每个条目由实际后继构造并证明唯一。 -/
theorem It_local_d.code_table_l {ω c X R c' Y S q Γ H k N T z : M.Domain}
    (hω : M.IsOmega ω) (ex : Rf_ext_d Kp X R) (mx : Smdl_d Kp c X R)
    (theory : Sc_theory_d Kp ω X R) (collection : Sc_collection_d Kp ω X R)
    (model : Smdl_d Kp c' Y S) (hq : Smap_d Kp ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (U w ξ ℓ f : (smdl_structure_l Kp (R := T) nx).Domain)
    (numbers : Rr_layer_d Kp ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l Kp (R := T) nx).Domain,
      (smdl_structure_l Kp (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l Kp (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d Kp N T U.val) (fk : M.IsSetInjectionFromTo Kp k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d Kp Y S H) (small : Rr_small_d Kp Y S H)
    (hξ : (smdl_structure_l Kp (R := T) nx).mem ξ U)
    (loc : It_local_d Kp w.val N T ξ.val ℓ.val f.val) :
    ∃ L J O Z Q, (∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T) ∧
      (∀ a, M.mem a J ↔ Ei_d ω L a) ∧ Di_order_d J O ∧
      (∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ r, Ei_map_d ω L a b r) ∧
      Fn0_d J Q Z ∧ ∀ a o, Rd_entry_d a o Z ↔ M.mem a J ∧ Er_code_d Kp ω L N T ξ.val f.val z Y S k a o := by
  let η₀ : Env M 2 := ⟨Fin.cases ℓ.val (fun _ => T), fun _ => N⟩
  let ψ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨L, ls⟩ := ZF.separation_exists_d hZF ψ η₀ N
  have length x : M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T :=
    (ls x).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
  obtain ⟨J, O, indices, order, os⟩ := ei_order_l (L := L) hZF hω
  let N₀ := smdl_structure_l Kp (R := T) nx
  have actual := loc.read_l Kp _ (kp_pair_l hN) hN.1 w ξ ℓ f
  let η : Env M 10 := ⟨Fin.cases k (Fin.cases S (Fin.cases Y (Fin.cases z (Fin.cases f.val
    (Fin.cases ξ.val (Fin.cases T (Fin.cases N (Fin.cases L (fun _ => ω))))))))), fun _ => ω⟩
  let φ : BinarySchema 10 := {
    body := er_code_m (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a o : φ.denote η a o ↔ Er_code_d Kp ω L N T ξ.val f.val z Y S k a o := er_code_sat_l Kp hZF.1 ..
  have total a (ha : M.mem a J) : ∃ o, φ.denote η a o := by
    obtain ⟨n, hn, fa, _⟩ := (indices a).mp ha
    obtain ⟨m, b, d, u, hnm, fn, graph, _, space, _, hbu,
      D, i, t, y, P, V, G, o, p, C, W, j, q', dc, fi, id, rt, _, hdy, _, _, _, _, measure, family, quotient, _⟩ :=
      loc.raw_reduced_l hZF hω ex mx theory collection model hq nx hN U w ξ ℓ f numbers finite powers
        carrier ownerClosed fk image pred closed small hξ length hn fa
    exact ⟨o, (sat a o).mpr ⟨n, m.val, b.val, d.val, u.val, D, i, t, y, V, G, p, C, W,
      hn, fa, hnm, fn, graph, (er_space_native_l Kp nx hN.1 ξ m d).mpr space,
      (rf_val_native_l Kp nx hN.1 b u f).mpr hbu, dc, fn0_of_function_l (ZF.modelsKP hZF) fi,
      id, rt, hdy, measure, family, quotient⟩⟩
  have unique a (_ : M.mem a J) o o' (ho : φ.denote η a o) (ho' : φ.denote η a o') : o = o' :=
    ((sat a o).mp ho).unique_l hZF numbers hN.1 ξ f actual.measures.function fk.1.1 ((sat a o').mp ho')
  obtain ⟨Q, qs⟩ := ZF.exists_functionalImageOn hZF φ η J total unique
  obtain ⟨Z, fZ, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ η total unique
    (fun a o ha ho => (qs o).mpr ⟨a, ha, ho⟩)
  exact ⟨L, J, O, Z, Q, length, indices, order, os, fn0_of_function_l (ZF.modelsKP hZF) fZ,
    fun a o => (graph a o).trans (and_congr Iff.rfl (sat a o))⟩

end Construction
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原对象码坐标过渡的统一公式

支撑在所属模型内重排，有限幂仍由所属模型计算。背景只展开同一投影图；
单射支撑决定唯一重排，故全部见证给出相同的定义域和坐标过渡。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Er_native_d (ξ L a b d e p : M.Domain) : Prop := ∃ m n r,
  Fn0_d m L a ∧ Fn0_d n L b ∧ Fn0_d m n r ∧ Cp0_d m n L r b a ∧
  Ep_space_d ξ m d ∧ Ep_space_d ξ n e ∧ Fn0_d e d p ∧
  ∀ s t, Rd_entry_d s t p ↔ M.mem s e ∧ Cp0_d m n ξ r s t

def er_native_m {n} (ξ L a b d e p : Term n) : Formula 1 n := set[n] ⟪∃ m n r,
  ⌜fn0_m⌝ₚ(m, ⌜L⌝ₛ, ⌜a⌝ₛ) ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜b⌝ₛ) ∧
  ⌜fn0_m⌝ₚ(m, n, r) ∧ ⌜cp0_m⌝ₚ(m, n, ⌜L⌝ₛ, r, ⌜b⌝ₛ, ⌜a⌝ₛ) ∧
  ⌜ep_space_m⌝ₚ(⌜ξ⌝ₛ, m, ⌜d⌝ₛ) ∧ ⌜ep_space_m⌝ₚ(⌜ξ⌝ₛ, n, ⌜e⌝ₛ) ∧
  ⌜fn0_m⌝ₚ(⌜e⌝ₛ, ⌜d⌝ₛ, ⌜p⌝ₛ) ∧
  (∀ s t, ⌜rd_entry0_m⌝ₚ(s, t, ⌜p⌝ₛ) ↔ s ∈ ⌜e⌝ₛ ∧ ⌜cp0_m⌝ₚ(m, n, ⌜ξ⌝ₛ, r, s, t))⟫
derive_free_closed er_native_m

theorem er_native_sat_l (ext : Extensional M) {n} (ρ : Env M n) (ξ L a b d e p : Term n) :
    Formula.satisfies ρ (er_native_m ξ L a b d e p) ↔
      Er_native_d (ξ.eval ρ) (L.eval ρ) (a.eval ρ) (b.eval ρ) (d.eval ρ) (e.eval ρ) (p.eval ρ) := by
  simp only [er_native_m, Er_native_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l ext, cp0_sat_l ext, ep_space_sat_l ext, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, rd_entry0_sat_l ext, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]; rfl

variable (I : kpair_convention_l.Interpretation M)

private def er_project_d (N T ξ L a b d e p : M.Domain) : Prop :=
  Rr_truth_d I (n := 6) N T
    (er_native_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (Fin.cases p (Fin.cases e (Fin.cases d (Fin.cases b (Fin.cases a (Fin.cases L (fun _ => ξ)))))))

private def er_project_m {n} (N T ξ L a b d e p : Term n) : Formula 1 n :=
  rr_truth_m (𝒞 := kpair_convention_l) (n := 6)
    (er_native_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) N T
    (Fin.cases p (Fin.cases e (Fin.cases d (Fin.cases b (Fin.cases a (Fin.cases L (fun _ => ξ)))))))

@[simp] private theorem er_project_closed_l {n} (N T ξ L a b d e p : Term n)
    (hN : N.freeSupport = []) (hT : T.freeSupport = []) (hξ : ξ.freeSupport = [])
    (hL : L.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = [])
    (hd : d.freeSupport = []) (he : e.freeSupport = []) (hp : p.freeSupport = []) :
    (er_project_m N T ξ L a b d e p).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) _ _ _ hN hT
    (Fin.cases hp (Fin.cases he (Fin.cases hd (Fin.cases hb (Fin.cases ha (Fin.cases hL (fun _ => hξ)))))))

private theorem er_project_sat_l {n} (ρ : Env M n) (N T ξ L a b d e p : Term n) :
    Formula.satisfies ρ (er_project_m N T ξ L a b d e p) ↔
      er_project_d I (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (L.eval ρ) (a.eval ρ) (b.eval ρ)
        (d.eval ρ) (e.eval ρ) (p.eval ρ) := by
  unfold er_project_m
  rw [rr_truth_sat_l I _ _ (by simp -implicitDefEqProofs)]
  have row : (fun i : Fin 7 => ((Fin.cases p (Fin.cases e (Fin.cases d (Fin.cases b
      (Fin.cases a (Fin.cases L (fun _ => ξ)))))) : Fin 7 → Term n) i).eval ρ) =
      Fin.cases (p.eval ρ) (Fin.cases (e.eval ρ) (Fin.cases (d.eval ρ) (Fin.cases (b.eval ρ)
        (Fin.cases (a.eval ρ) (Fin.cases (L.eval ρ) (fun _ => ξ.eval ρ)))))) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))))
  rw [row]
  rfl

private theorem er_project_native_l {N T : M.Domain} (nx : ∃ x, M.mem x N)
    (ext : Extensional (smdl_structure_l I (R := T) nx))
    (ξ L a b d e p : (smdl_structure_l I (R := T) nx).Domain) :
    er_project_d I N T ξ.val L.val a.val b.val d.val e.val p.val ↔ Er_native_d ξ L a b d e p := by
  rcases ξ with ⟨ξ, hξ⟩
  rcases L with ⟨L, hL⟩
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases d with ⟨d, hd⟩
  rcases e with ⟨e, he⟩
  rcases p with ⟨p, hp⟩
  let v : Fin 7 → M.Domain := Fin.cases p (Fin.cases e (Fin.cases d (Fin.cases b
    (Fin.cases a (Fin.cases L (fun _ => ξ))))))
  have hv : ∀ i, M.mem (v i) N := Fin.cases hp (Fin.cases he (Fin.cases hd (Fin.cases hb
    (Fin.cases ha (Fin.cases hL (fun _ => hξ))))))
  let ρ : Env (smdl_structure_l I (R := T) nx) 7 := ⟨fun i => ⟨v i, hv i⟩, fun _ => ⟨p, hp⟩⟩
  exact ⟨fun ⟨_, valid⟩ => (er_native_sat_l ext ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3)
    (.bound 2) (.bound 1) .newest).mp valid,
    fun h => ⟨hv, (er_native_sat_l ext ρ (.bound 6) (.bound 5) (.bound 4) (.bound 3)
      (.bound 2) (.bound 1) .newest).mpr h⟩⟩

def Er_coord_d (ω L N T ξ ℓ z a b D E t : M.Domain) : Prop := ∃ u v d e p,
  Rr_finite_d I ω L N T z a u ∧ Rr_finite_d I ω L N T z b v ∧
  er_project_d I N T ξ ℓ u v d e p ∧
  (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d T) ∧
  (∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e T) ∧ Fn0_d E D t ∧
  ∀ s q, M.mem s N → M.mem q N → (Rd_entry_d s q t ↔ Rf_val_d I N T s q p)

def er_coord_m {n} (ω L N T ξ ℓ z a b D E t : Term n) : Formula 1 n := set[n] ⟪∃ u v d e p,
  ⌜rr_finite_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜z⌝ₛ, ⌜a⌝ₛ, u) ∧
  ⌜rr_finite_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜z⌝ₛ, ⌜b⌝ₛ, v) ∧
  ⌜er_project_m⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜ℓ⌝ₛ, u, v, d, e, p) ∧
  (∀ x, x ∈ ⌜D⌝ₛ ↔ x ∈ ⌜N⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x, d, ⌜T⌝ₛ)) ∧
  (∀ x, x ∈ ⌜E⌝ₛ ↔ x ∈ ⌜N⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x, e, ⌜T⌝ₛ)) ∧
  ⌜fn0_m⌝ₚ(⌜E⌝ₛ, ⌜D⌝ₛ, ⌜t⌝ₛ) ∧
  (∀ s ∈ ⌜N⌝ₛ, ∀ q ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(s, q, ⌜t⌝ₛ) ↔
    ⌜rf_val_m (𝒞 := kpair_convention_l)⌝ₚ(⌜N⌝ₛ, ⌜T⌝ₛ, s, q, p))⟫
derive_free_closed er_coord_m

theorem er_coord_sat_l (ext : Extensional M) {n} (ρ : Env M n) (ω L N T ξ ℓ z a b D E t : Term n) :
    Formula.satisfies ρ (er_coord_m ω L N T ξ ℓ z a b D E t) ↔
      Er_coord_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (ℓ.eval ρ)
        (z.eval ρ) (a.eval ρ) (b.eval ρ) (D.eval ρ) (E.eval ρ) (t.eval ρ) := by
  simp only [er_coord_m, Er_coord_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rr_finite_sat_l I ext, er_project_sat_l I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l ext, fn0_sat_l ext, Formula.satisfies_forallMem_iff,
    rf_val_sat_l I, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨u, v, d, e, p, hu, hv, hp, dc, ec, ft, gr⟩ =>
    ⟨u, v, d, e, p, hu, hv, hp, dc, ec, ft, fun s q hs hq => gr s hs q hq⟩,
    fun ⟨u, v, d, e, p, hu, hv, hp, dc, ec, ft, gr⟩ =>
    ⟨u, v, d, e, p, hu, hv, hp, dc, ec, ft, fun s hs q hq => gr s q hs hq⟩⟩

theorem Er_coord_d.of_native_l {ω L N T z a b D E t : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := T) nx))
    (ξ ℓ u v d e p : (smdl_structure_l I (R := T) nx).Domain)
    (ha : Rr_finite_d I ω L N T z a u.val) (hb : Rr_finite_d I ω L N T z b v.val)
    (native : Er_native_d ξ ℓ u v d e p)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T)
    (ec : ∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T) (ft : Fn0_d E D t)
    (graph : ∀ s q : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val q.val t ↔ Rd_entry_d s q p) :
    Er_coord_d I ω L N T ξ.val ℓ.val z a b D E t :=
  ⟨u.val, v.val, d.val, e.val, p.val, ha, hb, (er_project_native_l I nx ext ..).mpr native,
    dc, ec, ft, fun s q hs hq => (graph ⟨s, hs⟩ ⟨q, hq⟩).trans (rf_val_native_l I nx ext ..).symm⟩

theorem Er_coord_d.read_l {ω L N T z a b D E t : M.Domain}
    (nx : ∃ x, M.mem x N) (ext : Extensional (smdl_structure_l I (R := T) nx))
    (ξ ℓ : (smdl_structure_l I (R := T) nx).Domain)
    (h : Er_coord_d I ω L N T ξ.val ℓ.val z a b D E t) :
    ∃ u v d e p : (smdl_structure_l I (R := T) nx).Domain,
      Rr_finite_d I ω L N T z a u.val ∧ Rr_finite_d I ω L N T z b v.val ∧ Er_native_d ξ ℓ u v d e p ∧
      (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) ∧
      (∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T) ∧ Fn0_d E D t ∧
      ∀ s q : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val q.val t ↔ Rd_entry_d s q p := by
  obtain ⟨u, v, d, e, p, hu, hv, hp, dc, ec, ft, graph⟩ := h
  have bound := hp.elim (fun h _ => h)
  let u' := (⟨u, bound 4⟩ : (smdl_structure_l I (R := T) nx).Domain)
  let v' := (⟨v, bound 3⟩ : (smdl_structure_l I (R := T) nx).Domain)
  let d' := (⟨d, bound 2⟩ : (smdl_structure_l I (R := T) nx).Domain)
  let e' := (⟨e, bound 1⟩ : (smdl_structure_l I (R := T) nx).Domain)
  let p' := (⟨p, bound 0⟩ : (smdl_structure_l I (R := T) nx).Domain)
  exact ⟨u', v', d', e', p', hu, hv, (er_project_native_l I nx ext ξ ℓ u' v' d' e' p').mp hp,
    dc, ec, ft, fun s q => (graph s.val q.val s.property q.property).trans (rf_val_native_l I nx ext s q p')⟩

section Unique
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 规范性同时固定两侧对象码载体及展开图，不选择支撑排列。 -/
theorem Er_coord_d.unique_l {ω L N T z a b D E t D' E' t' w : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ξ ℓ : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (inside : M.MemberSubset L N)
    (inj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j)
    (h : Er_coord_d Kp ω L N T ξ.val ℓ.val z a b D E t)
    (h' : Er_coord_d Kp ω L N T ξ.val ℓ.val z a b D' E' t') : D = D' ∧ E = E' ∧ t = t' := by
  let nx := (⟨w, numbers.member⟩ : ∃ x, M.mem x N)
  let N₀ := smdl_structure_l Kp (R := T) nx
  obtain ⟨u, v, d, e, p, hu, hv, native, dc, ec, ft, graph⟩ := h.read_l Kp nx ext ξ ℓ
  obtain ⟨u', v', d', e', p', hu', hv', native', dc', ec', ft', graph'⟩ := h'.read_l Kp nx ext ξ ℓ
  have eq : u' = u := Subtype.ext (hu'.unique_l hZF numbers ext hu)
  subst u'
  have eq : v' = v := Subtype.ext (hv'.unique_l hZF numbers ext hv)
  subst v'
  obtain ⟨m, n, r, fa, fb, fr, factor, ds, es, fp, ps⟩ := native
  obtain ⟨m', n', r', fa', fb', fr', factor', ds', es', fp', ps'⟩ := native'
  have eq := fa'.domain_eq_l ext fa
  subst m'
  have eq := fb'.domain_eq_l ext fb
  subst n'
  have eq := ext.eq_of_same_members d' d (fun x => (ds' x).trans (ds x).symm)
  subst d'
  have eq := ext.eq_of_same_members e' e (fun x => (es' x).trans (es x).symm)
  subst e'
  have vb := hv
  obtain ⟨n₀, n₁, _, fvb, hn, fn, gv⟩ := vb
  let n₂ : N₀.Domain := ⟨n₁, numbers.injection.1.output_mem_of_pairMember hn⟩
  obtain ⟨A, fA⟩ := (rf_fun_native_l Kp nx ext n₂ v).mp fn
  have en : n₁ = n.val := congrArg (fun x : N₀.Domain => x.val) (fA.domain_eq_l ext fb)
  have nativeInj := (numbers.function_injective_l hZF ext n ℓ v (en ▸ hn) fb
    (fvb.mono_target_l inside) gv).mp inj
  have eq := ec_factor_unique_l ext nativeInj fr' fr factor' factor
  subst r'
  have eq := fp'.ext_l ext fp (fun s hs => by
    obtain ⟨q, _, hsq⟩ := fp'.2.1 s hs
    exact ⟨q, hsq, (ps s q).mpr ((ps' s q).mp hsq)⟩)
  subst p'
  have eqD := hZF.1.eq_of_same_members D D' (fun x => (dc x).trans (dc' x).symm)
  have eqE := hZF.1.eq_of_same_members E E' (fun x => (ec x).trans (ec' x).symm)
  subst D'
  subst E'
  refine ⟨rfl, rfl, ft.ext_l hZF.1 ft' ?_⟩
  intro s hs
  obtain ⟨q, hq, hsq⟩ := ft.2.1 s hs
  let s₀ : N₀.Domain := ⟨s, ((ec s).mp hs).1⟩
  let q₀ : N₀.Domain := ⟨q, ((dc q).mp hq).1⟩
  exact ⟨q, hsq, (graph' s₀ q₀).mpr ((graph s₀ q₀).mp hsq)⟩

end Unique

section NativeRead
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意坐标见证都可按给定的两个原支撑及其有限幂规范化。 -/
theorem Er_coord_d.native_l {ω L N T w z A B D E t : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (ext : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ξ ℓ m n a b d e : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (ca : Rr_finite_d Kp ω L N T z A a.val) (cb : Rr_finite_d Kp ω L N T z B b.val)
    (fa : Fn0_d m ℓ a) (fb : Fn0_d n ℓ b) (ds : Ep_space_d ξ m d) (es : Ep_space_d ξ n e)
    (h : Er_coord_d Kp ω L N T ξ.val ℓ.val z A B D E t) :
    (∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) ∧
    (∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x e.val T) ∧ Fn0_d E D t ∧
    ∃ q p : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain,
      Fn0_d m n q ∧ Cp0_d m n ℓ q b a ∧ Fn0_d e d p ∧
      (∀ s v, Rd_entry_d s v p ↔ (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).mem s e ∧ Cp0_d m n ξ q s v) ∧
      ∀ s v : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain, Rd_entry_d s.val v.val t ↔ Rd_entry_d s v p := by
  obtain ⟨a', b', d', e', p, ca', cb', native, dc, ec, ft, graph⟩ :=
    h.read_l Kp ⟨w, numbers.member⟩ ext ξ ℓ
  obtain ⟨m', n', q, fa', fb', fq, factor, ds', es', fp, ps⟩ := native
  have eq : a' = a := Subtype.ext (ca'.unique_l hZF numbers ext ca)
  subst a'
  have eq : b' = b := Subtype.ext (cb'.unique_l hZF numbers ext cb)
  subst b'
  have eq := fa'.domain_eq_l ext fa
  subst m'
  have eq := fb'.domain_eq_l ext fb
  subst n'
  have eq := ext.eq_of_same_members d' d (fun x => (ds' x).trans (ds x).symm)
  subst d'
  have eq := ext.eq_of_same_members e' e (fun x => (es' x).trans (es x).symm)
  subst e'
  exact ⟨dc, ec, ft, q, p, fq, factor, fp, ps, graph⟩

end NativeRead


section Laws
variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_coord_d.refl_l {ω L N T z a D : M.Domain}
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l Kp (R := T) nx).Models KP)
    (ξ ℓ m u d : (smdl_structure_l Kp (R := T) nx).Domain)
    (ha : Rr_finite_d Kp ω L N T z a u.val) (fa : Fn0_d m ℓ u) (ds : Ep_space_d ξ m d)
    (dc : ∀ x, M.mem x D ↔ M.mem x N ∧ Rd_entry_d x d.val T) :
    ∃ t, Er_coord_d Kp ω L N T ξ.val ℓ.val z a a D D t ∧
      ∀ x y, Rd_entry_d x y t ↔ M.mem x D ∧ x = y := by
  obtain ⟨r, fr, ir⟩ := fn0_identity_l hN m
  have factor : Cp0_d m m ℓ r u u := ⟨fa, fun x hx => by
    obtain ⟨y, hy, hxy⟩ := fa.2.1 x hx
    exact ⟨x, hx, y, hy, (ir x x).mpr ⟨hx, rfl⟩, hxy, hxy⟩⟩
  obtain ⟨p, fp, ps⟩ := cp0_projection_l hN fr ds ds
  obtain ⟨E, F, t, ec, fc, ft, graph⟩ := smdl_graph_l hZF nx hN.1 d d p fp
  have eq := hZF.1.eq_of_same_members E D (fun x => (ec x).trans (dc x).symm)
  subst E
  have eq := hZF.1.eq_of_same_members F D (fun x => (fc x).trans (dc x).symm)
  subst F
  exact ⟨t, Er_coord_d.of_native_l Kp nx hN.1 ξ ℓ u u d d p ha ha
    ⟨m, m, r, fa, fa, fr, factor, ds, ds, fp, ps⟩ dc dc ft graph,
    smdl_graph_identity_l Kp nx d p dc ft graph (cp0_projection_id_l (fun x hx => (ds x).mp hx) fp ir ps)⟩

/-- 两次实际重排生成第三个实际重排；只在共同中间支撑处识别对象。 -/
theorem Er_coord_d.comp_l {ω L N T z a b c D E E' F t s w : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z)
    (hN : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Models KP)
    (ξ ℓ : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (h : Er_coord_d Kp ω L N T ξ.val ℓ.val z a b D E t)
    (g : Er_coord_d Kp ω L N T ξ.val ℓ.val z b c E' F s) :
    E' = E ∧ ∃ r, Er_coord_d Kp ω L N T ξ.val ℓ.val z a c D F r ∧ Cp0_d F E D s t r := by
  let nx := (⟨w, numbers.member⟩ : ∃ x, M.mem x N)
  obtain ⟨u, v, d, e, p, hu, hv, native, dc, ec, _, graph⟩ := h.read_l Kp nx hN.1 ξ ℓ
  obtain ⟨v', x, e', f, q, hv', hx, native', ec', fc, _, graph'⟩ := g.read_l Kp nx hN.1 ξ ℓ
  have eq : v' = v := Subtype.ext (hv'.unique_l hZF numbers hN.1 hv)
  subst v'
  obtain ⟨m, n, r, fa, fb, fr, factor, ds, es, fp, ps⟩ := native
  obtain ⟨n', l, r', fb', fc', fr', factor', es', fs, fq, qs⟩ := native'
  have eq := fb'.domain_eq_l hN.1 fb
  subst n'
  have eq := hN.1.eq_of_same_members e' e (fun x => (es' x).trans (es x).symm)
  subst e'
  have eq := hZF.1.eq_of_same_members E' E (fun x => (ec' x).trans (ec x).symm)
  subst E'
  obtain ⟨r'', comp⟩ := cp0_exists_l hN fr fr'
  obtain ⟨p', fp', ps'⟩ := cp0_projection_l hN comp.1 fs ds
  have nativeComp := cp0_projection_comp_l fr fr' comp (fun x hx => (fs x).mp hx) fp fq fp'
    (fun x y h => ((ps x y).mp h).2) (fun x y h => ((qs x y).mp h).2)
    (fun x y hx h => (ps' x y).mpr ⟨hx, h⟩)
  obtain ⟨F', D', t', fc'', dc', ft', graph''⟩ := smdl_graph_l hZF nx hN.1 f d p' fp'
  have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
  subst D'
  have eq := hZF.1.eq_of_same_members F' F (fun x => (fc'' x).trans (fc x).symm)
  subst F'
  exact ⟨rfl, t', Er_coord_d.of_native_l Kp nx hN.1 ξ ℓ u x d f p' hu hx
    ⟨m, l, r'', fa, fc', comp.1, Cp0_d.assoc_l fr' fr comp fc' factor' factor, ds, fs, fp', ps'⟩ dc fc ft' graph'',
    smdl_graph_composition_l Kp nx d e f p q p' dc ec fc ft' graph graph' graph'' nativeComp⟩

end Laws
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 带实际支撑的原关系商类复制

统一公式同时记录两个原分量及支撑逐点像。分量数据的唯一性将任意
公式见证读回原商和原坐标，供全部支撑上的同一节点图使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Er_class_d (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B' : M.Domain) : Prop :=
  ∃ o o' n m b d u D i t y V G p C W m' b' d' u' E i' t' y' V' H q C' W',
    Er_frame_d I ω L N T ξ F z X R k a o n m b d u D i t y V G p C W ∧
    Er_frame_d I ω L' N' T' ξ' F' z' Y S k' a' o' n m' b' d' u' E i' t' y' V' H q C' W' ∧
    Smap_assign_d I n σ a a' ∧ M.mem B C ∧ M.mem B' C' ∧ Rc_class_d I X R y t Y S t' π B B'

def er_class_m {v} (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B' : Term v) : Formula 1 v := set[v] ⟪
  ∃ o o' n m b d u D i t y V G p C W m' b' d' u' E i' t' y' V' H q C' W',
    ⌜er_frame_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜N⌝ₛ, ⌜T⌝ₛ, ⌜ξ⌝ₛ, ⌜F⌝ₛ, ⌜z⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜k⌝ₛ,
      ⌜a⌝ₛ, o, n, m, b, d, u, D, i, t, y, V, G, p, C, W) ∧
    ⌜er_frame_m⌝ₚ(⌜ω⌝ₛ, ⌜L'⌝ₛ, ⌜N'⌝ₛ, ⌜T'⌝ₛ, ⌜ξ'⌝ₛ, ⌜F'⌝ₛ, ⌜z'⌝ₛ, ⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜k'⌝ₛ,
      ⌜a'⌝ₛ, o', n, m', b', d', u', E, i', t', y', V', H, q, C', W') ∧
    ⌜smap_assign_m (𝒞 := kpair_convention_l)⌝ₚ(n, ⌜σ⌝ₛ, ⌜a⌝ₛ, ⌜a'⌝ₛ) ∧ ⌜B⌝ₛ ∈ C ∧ ⌜B'⌝ₛ ∈ C' ∧
    ⌜rc_class_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, y, t, ⌜Y⌝ₛ, ⌜S⌝ₛ, t', ⌜π⌝ₛ, ⌜B⌝ₛ, ⌜B'⌝ₛ)⟫

derive_free_closed er_class_m

theorem er_class_sat_l (ext : Extensional M) {v} (ρ : Env M v)
    (ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B' : Term v) :
    Formula.satisfies ρ (er_class_m ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B') ↔
      Er_class_d I (ω.eval ρ) (L.eval ρ) (N.eval ρ) (T.eval ρ) (ξ.eval ρ) (F.eval ρ) (z.eval ρ)
        (X.eval ρ) (R.eval ρ) (k.eval ρ) (L'.eval ρ) (N'.eval ρ) (T'.eval ρ) (ξ'.eval ρ) (F'.eval ρ) (z'.eval ρ)
        (Y.eval ρ) (S.eval ρ) (k'.eval ρ) (π.eval ρ) (σ.eval ρ) (a.eval ρ) (a'.eval ρ) (B.eval ρ) (B'.eval ρ) := by
  simp only [er_class_m, Er_class_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    er_frame_sat_l I ext, smap_assign_sat_l I, Formula.satisfies_mem_iff, rc_class_sat_l I ext,
    Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

/-- 合法原支撑的逐点复制仍是合法目标索引，所有点来自给定所属图。 -/
theorem Er_class_d.support_l
    {ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B' : M.Domain}
    (inside : M.MemberSubset L N) (map : M.IsSetInjectionFromTo Kp σ N N')
    (index : Ei_d ω L a)
    (h : Er_class_d Kp ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' B B') : Ei_d ω L' a' := by
  obtain ⟨_, _, n, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, source, target, assign, _⟩ := h
  have fa := source.2.1
  have fa' := target.2.1
  obtain ⟨n₀, _, fa₀, inj⟩ := index
  have eq := fa₀.domain_eq_l hZF.1 fa
  subst n₀
  refine ⟨n, source.1, fa', fun i j y hiy hjy => ?_⟩
  obtain ⟨x, hx, hix⟩ := fa.2.1 i (fa'.bound_l hiy).1
  obtain ⟨v, hv, hjv⟩ := fa.2.1 j (fa'.bound_l hjy).1
  obtain ⟨x', _, hxx⟩ := map.1.2.2 x (inside x hx)
  obtain ⟨v', _, hvv⟩ := map.1.2.2 v (inside v hv)
  have ix := assign i (fa'.bound_l hiy).1 x x' hix hxx
  have jv := assign j (fa'.bound_l hjy).1 v v' hjv hvv
  have ex := (fn0_function_l (ZF.modelsKP hZF) fa').1.2 i x' y ix hiy
  have ev := (fn0_function_l (ZF.modelsKP hZF) fa').1.2 j v' y jv hjy
  exact inj i j x hix (map.2 v x y (ev ▸ hvv) (ex ▸ hxx) ▸ hjv)

/-- 给定原支撑与所属图后，类公式中的目标支撑等于实际逐点像。 -/
theorem Er_class_d.support_eq_l
    {ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a' a'' B B' n : M.Domain}
    (inside : M.MemberSubset L N) (map : M.IsSetFunctionFromTo Kp σ N N')
    (fa : Fn0_d n L a) (fa' : Fn0_d n L' a') (assign : Smap_assign_d Kp n σ a a')
    (h : Er_class_d Kp ω L N T ξ F z X R k L' N' T' ξ' F' z' Y S k' π σ a a'' B B') : a'' = a' := by
  obtain ⟨_, _, n₀, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, source, target, assign₀, _⟩ := h
  have eq := source.2.1.domain_eq_l hZF.1 fa
  subst n₀
  apply Fn0_d.ext_l hZF.1 target.2.1 fa'
  intro i hi
  obtain ⟨x, hx, hix⟩ := fa.2.1 i hi
  obtain ⟨y, _, hxy⟩ := map.2.2 x (inside x hx)
  exact ⟨y, assign₀ i hi x y hix hxy, assign i hi x y hix hxy⟩

/-- 任意分量见证均归一到同一实际商，统一类公式准确读取原复制。 -/
theorem Er_class_d.read_l
    {ω L N T w z X R k L' N' T' w' z' Y S k' π σ a a' B B' o o' n m b d u D i t y V G p C W
      m' b' d' u' E i' t' y' V' H q C' W' : M.Domain}
    (numbers : Rr_layer_d Kp ω N T w z) (numbers' : Rr_layer_d Kp ω N' T' w' z')
    (ex : Extensional (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩))
    (ey : Extensional (smdl_structure_l Kp (R := T') ⟨w', numbers'.member⟩))
    (ξ f : (smdl_structure_l Kp (R := T) ⟨w, numbers.member⟩).Domain)
    (ξ' f' : (smdl_structure_l Kp (R := T') ⟨w', numbers'.member⟩).Domain)
    (single : ∀ b u v, Rd_entry_d b u f → Rd_entry_d b v f → u = v)
    (single' : ∀ b u v, Rd_entry_d b u f' → Rd_entry_d b v f' → u = v)
    (fk : M.IsSetFunction Kp k) (fk' : M.IsSetFunction Kp k')
    (source : Er_frame_d Kp ω L N T ξ.val f.val z X R k a o n m b d u D i t y V G p C W)
    (target : Er_frame_d Kp ω L' N' T' ξ'.val f'.val z' Y S k' a' o' n m' b' d' u' E i' t' y' V' H q C' W') :
    Er_class_d Kp ω L N T ξ.val f.val z X R k L' N' T' ξ'.val f'.val z' Y S k' π σ a a' B B' ↔
      Smap_assign_d Kp n σ a a' ∧ M.mem B C ∧ M.mem B' C' ∧ Rc_class_d Kp X R y t Y S t' π B B' := by
  constructor
  · rintro ⟨o₀, o₁, n₀, m₀, b₀, d₀, u₀, D₀, i₀, t₀, y₀, V₀, G₀, p₀, C₀, W₀,
      m₁, b₁, d₁, u₁, E₁, i₁, t₁, y₁, V₁, H₁, q₁, C₁, W₁, hs, ht, assign, hB, hB', copy⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      source.unique_l hZF numbers ex ξ f single fk hs
    obtain ⟨rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      target.unique_l hZF numbers' ey ξ' f' single' fk' ht
    exact ⟨assign, hB, hB', copy⟩
  · rintro ⟨assign, hB, hB', copy⟩
    exact ⟨o, o', n, m, b, d, u, D, i, t, y, V, G, p, C, W,
      m', b', d', u', E, i', t', y', V', H, q, C', W', source, target, assign, hB, hB', copy⟩

end YesMetaZFC.SetTheory.LargeCardinal
