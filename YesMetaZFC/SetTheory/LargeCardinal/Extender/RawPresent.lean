import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.Collapse.RelationRealization

/-! # 原共同支撑约束的函数复合形式

坐标投影使用同一个原重排。共同支撑上的逐点成员条件，正是两个
原复合函数的逐点关系；有限列全集只用于界定已有见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)

theorem eb_point_pull_l {ω κ B K R m n l q r d e v p t f g f' g' s : M.Domain}
    (finite : Fseq_space_d (kp_pair_l hKP) ω κ K) (hm : M.mem m ω) (hn : M.mem n ω)
    (ds : Ep_space_d κ m d) (es : Ep_space_d κ n e)
    (fp : Fn0_d v d p) (ft : Fn0_d v e t) (ff : Fn0_d d B f) (fg : Fn0_d e B g)
    (ps : ∀ s u, Rd_entry_d s u p ↔ M.mem s v ∧ Cp0_d m l κ q s u)
    (ts : ∀ s u, Rd_entry_d s u t ↔ M.mem s v ∧ Cp0_d n l κ r s u)
    (cf : Cp0_d v d B p f f') (cg : Cp0_d v e B t g g') (hs : M.mem s v) :
    Eb_point_d κ B K R m n l q r f g s ↔
      ∃ x, M.mem x B ∧ ∃ y, M.mem y B ∧ Rd_entry_d s x f' ∧ Rd_entry_d s y g' ∧ Rd_entry_d x y R := by
  constructor
  · rintro ⟨u, _, v, _, x, hx, y, hy, cu, cv, hux, hvy, hxy⟩
    exact ⟨x, hx, y, hy, (cf.value_l fp ff ((ps s u).mpr ⟨hs, cu⟩)).mpr hux,
      (cg.value_l ft fg ((ts s v).mpr ⟨hs, cv⟩)).mpr hvy, hxy⟩
  · rintro ⟨x, hx, y, hy, hsx, hsy, hxy⟩
    obtain ⟨u, hu, hsu⟩ := fp.2.1 s hs
    obtain ⟨v, hv, hsv⟩ := ft.2.1 s hs
    exact ⟨u, (finite u).mpr ⟨m, hm, fn0_function_l hKP ((ds u).mp hu)⟩,
      v, (finite v).mpr ⟨n, hn, fn0_function_l hKP ((es v).mp hv)⟩, x, hx, y, hy,
      ((ps s u).mp hsu).2, ((ts s v).mp hsv).2, (cf.value_l fp ff hsu).mp hsx, (cg.value_l ft fg hsv).mp hsy, hxy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际支撑边的原函数解释

先按原支撑及有限幂规范化坐标边，再在所属模型内复合原函数。
当前源中的已给定代表由这一个原复合函数精确读出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Er_coord_d.pull_l {ω L N T w z A B D D' E t Γ Y k F g h : M.Domain}
    (numbers : Rr_layer_d I ω N T w z)
    (hN : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Models KP)
    (ξ ℓ m n a b d e β f : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (ca : Rr_finite_d I ω L N T z A a.val) (cb : Rr_finite_d I ω L N T z B b.val)
    (fa : Fn0_d m ℓ a) (fb : Fn0_d n ℓ b) (ds : Ep_space_d ξ m d) (es : Ep_space_d ξ n e)
    (ff : Fn0_d d β f) (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T)
    (fk : M.IsSetFunctionFromTo I k Γ Y) (fF : Fn0_d D Γ F)
    (gF : ∀ s v : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f)
    (value : Cp0_d D Γ Y F k g) (pull : Cp0_d E D' Y t g h)
    (coord : Er_coord_d I ω L N T ξ.val ℓ.val z A B D' E t) :
    (∀ s, M.mem s E ↔ M.mem s N ∧ Rd_entry_d s e.val T) ∧
    ∃ q p f' : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain, ∃ F',
      Fn0_d m n q ∧ Cp0_d m n ℓ q b a ∧ Fn0_d e d p ∧
      (∀ s v, Rd_entry_d s v p ↔ (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).mem s e ∧ Cp0_d m n ξ q s v) ∧
      Cp0_d e d β p f f' ∧ Fn0_d E Γ F' ∧
      (∀ s v : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain, Rd_entry_d s.val v.val F' ↔ Rd_entry_d s v f') ∧
      Cp0_d E Γ Y F' k h := by
  obtain ⟨dc', ec, _, q, p, fq, factor, fp, ps, graph⟩ := coord.native_l hZF numbers hN.1 ξ ℓ m n a b d e ca cb fa fb ds es
  have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
  subst D'
  obtain ⟨f', comp⟩ := cp0_exists_l hN fp ff
  obtain ⟨F', fF', grF', value'⟩ := rr_cross_pull_l hZF ⟨w, numbers.member⟩ hN.1 d e β p f f'
    fp ff comp dc ec fk fF graph gF value pull
  exact ⟨ec, q, p, f', F', fq, factor, fp, ps, comp, fF', grF', value'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型有限支撑的反向读取

自然数坐标覆盖全部内部有限长度。原支撑及原共同支撑沿同一坐标图
解码，支撑包含只需读取实际取值，不要求支撑值位于共同低层。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem er_index_decode_l {ω L N T w z : M.Domain}
    (numbers : Rr_layer_d I ω N T w z)
    (ext : Extensional (smdl_structure_l I (R := T) ⟨w, numbers.member⟩))
    (ℓ a : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (index : Ei_d (⟨w, numbers.member⟩ : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain) ℓ a) :
    ∃ A, Ei_d ω L A ∧ Rr_finite_d I ω L N T z A a.val := by
  obtain ⟨m, hm, fa, inj⟩ := index
  obtain ⟨n, hn, hnm⟩ := (numbers.image m.val).mp hm
  obtain ⟨A, fA, graph⟩ := numbers.function_decode_l hZF ext m ℓ a hnm fa length
  have injA := (numbers.function_injective_l hZF ext m ℓ a hnm fa
    (fA.mono_target_l (fun x hx => ((length x).mp hx).1)) graph).mpr inj
  exact ⟨A, ⟨n, hn, fA, injA⟩, n, m.val, hn, fA, hnm,
    (rf_fun_native_l I _ ext m a).mpr ⟨ℓ, fa⟩, graph⟩

/-- 原支撑的实际包含方程产生背景中的真实重排图。 -/
theorem er_support_factor_l {ω L N T w z A B : M.Domain}
    (numbers : Rr_layer_d I ω N T w z)
    (ext : Extensional (smdl_structure_l I (R := T) ⟨w, numbers.member⟩))
    (m n ℓ a b q : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (fa : Rr_finite_d I ω L N T z A a.val) (fb : Rr_finite_d I ω L N T z B b.val)
    (native : Fn0_d n ℓ b) (factor : Cp0_d m n ℓ q b a)
    (inj : ∀ i j x, Rd_entry_d i x B → Rd_entry_d j x B → i = j) :
    ∃ r, Ei_map_d ω L A B r := by
  let N₀ := smdl_structure_l I (R := T) ⟨w, numbers.member⟩
  obtain ⟨m₀, m₁, hm₀, fA, hmm, fna, ga⟩ := fa
  obtain ⟨n₀, n₁, hn₀, fB, hnn, fnb, gb⟩ := fb
  let m' : N₀.Domain := ⟨m₁, numbers.injection.1.output_mem_of_pairMember hmm⟩
  let n' : N₀.Domain := ⟨n₁, numbers.injection.1.output_mem_of_pairMember hnn⟩
  obtain ⟨X, fm⟩ := (rf_fun_native_l I _ ext m' a).mp fna
  obtain ⟨Y, fn⟩ := (rf_fun_native_l I _ ext n' b).mp fnb
  have em : m₁ = m.val := congrArg (fun x : N₀.Domain => x.val) (fm.domain_eq_l ext factor.1)
  have en : n₁ = n.val := congrArg (fun x : N₀.Domain => x.val) (fn.domain_eq_l ext native)
  have hmm : Rd_entry_d m₀ m.val z := em ▸ hmm
  have hnn : Rd_entry_d n₀ n.val z := en ▸ hnn
  obtain ⟨r, fr, comp⟩ := ec_factor_l hZF fA ⟨fn0_function_l (ZF.modelsKP hZF) fB, inj⟩ (fun i x hix => by
    obtain ⟨i₀, hi₀, hii⟩ := numbers.injection.1.2.2 i
      (numbers.transitive m₀ (numbers.injection.1.input_mem_of_pairMember hmm) i (fA.bound_l hix).1)
    have val := (ga i i₀ x hii).mp hix
    let i' : N₀.Domain := ⟨i₀, hi₀⟩
    let x' : N₀.Domain := ⟨x, (val.bounds_l I).2.1⟩
    have hia := (rf_val_native_l I _ ext i' x' a).mp val
    obtain ⟨j, hj, y, hy, _, hby, hay⟩ := factor.2 i' (factor.1.bound_l hia).1
    have eq := factor.1.2.2 i' (factor.1.bound_l hia).1 y hy x' (factor.1.bound_l hia).2 hay hia
    obtain ⟨j₀, _, hjj⟩ := (numbers.predecessors n₀ n.val hnn j.val).mp hj
    exact ⟨j₀, (gb j₀ j.val x hjj).mpr ((rf_val_native_l I _ ext j x' b).mpr (eq ▸ hby))⟩)
  exact ⟨r, m₀, n₀, hm₀, hn₀, fr, fB, comp⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原有界池约束与对象码极限关系

两个方向使用同一个原共同支撑及原测度。支撑沿自然数坐标读取，
原函数在所属模型内复合，测度一集合沿完整对象码图取迹。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.code_edge_l {ω c X R c' Y S q Γ H k N T z L J O Z A p V W r C W'
    a b D Q F G f₀ g₀ E H₀ : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (powers : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
        ∃ p, (smdl_structure_l I (R := T) nx).IsPowerSetOf p d)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (m n a' b' d d₁ β J₀ K₀ V₀ R₀ f g : (smdl_structure_l I (R := T) nx).Domain)
    (indices : ∀ a, (smdl_structure_l I (R := T) nx).mem a J₀ ↔ Ei_d w ℓ a)
    (nativeFinite : Fseq_space_d (kp_pair_l hN) w ξ K₀)
    (measures : ∀ a μ, Rd_entry_d a μ e → (smdl_structure_l I (R := T) nx).mem μ V₀)
    (member : Rd_fun_d .mem β β β R₀)
    (hm : (smdl_structure_l I (R := T) nx).mem m w) (hn : (smdl_structure_l I (R := T) nx).mem n w)
    (codeA : Rr_finite_d I ω L N T z a a'.val) (codeB : Rr_finite_d I ω L N T z b b'.val)
    (fa : Fn0_d m ℓ a') (fb : Fn0_d n ℓ b') (ds : Ep_space_d ξ m d) (qs : Ep_space_d ξ n d₁)
    (ff : Fn0_d d β f) (fg : Fn0_d d₁ β g)
    (dc : ∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T)
    (qc : ∀ s, M.mem s Q ↔ M.mem s N ∧ Rd_entry_d s d₁.val T)
    (fF : Fn0_d D Γ F) (fG : Fn0_d Q Γ G)
    (grF : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f)
    (grG : ∀ s v : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d s.val v.val G ↔ Rd_entry_d s v g)
    (cf : Cp0_d D Γ Y F k f₀) (cg : Cp0_d Q Γ Y G k g₀)
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    (fv : Ep_repr_d r a f₀ E) (gv : Ep_repr_d r b g₀ H₀)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) :
    Eb_edge_d w ξ ℓ β J₀ K₀ V₀ R₀ e a' f b' g ↔ Rd_entry_d E H₀ W' := by
  let N₀ := smdl_structure_l I (R := T) nx
  have actual := loc.read_l I _ (kp_pair_l hN) hN.1 w ξ ℓ e
  obtain ⟨_, table⟩ := h.codes
  constructor
  · rintro ⟨c₀, hc₀, μ, _, hcμ, B₀, hBμ, m₀, _, n₀, _, l, hl, σ, _, τ, _, fσ, fτ, fc, fσa, fτb, point⟩
    have eq := fσa.1.domain_eq_l hN.1 fa
    subst m₀
    have eq := fτb.1.domain_eq_l hN.1 fb
    subst n₀
    have index := (indices c₀).mp hc₀
    obtain ⟨χ, hχ, codeC⟩ := er_index_decode_l hZF numbers hN.1 ℓ c₀ length index
    have hχJ := (h.indices χ).mpr hχ
    obtain ⟨_, _, _, inj⟩ := hχ
    obtain ⟨_, _, _, nativeInj⟩ := index
    obtain ⟨s₀, edge₀⟩ := er_support_factor_l hZF numbers hN.1 m l ℓ a' c₀ σ codeA codeC fc fσa inj
    obtain ⟨s₁, edge₁⟩ := er_support_factor_l hZF numbers hN.1 n l ℓ b' c₀ τ codeB codeC fc fτb inj
    obtain ⟨o, _, hχo⟩ := table.2.1 χ hχJ
    obtain ⟨i, l', c₁, d₂, μ', hi, fχ, hil, fnχ, grχ, fc', space, _, hcμ',
      D₂, i₂, t₂, d₂', P₂, U₂, G₂, p₂, C₂, W₂, dc₂, fi₂, id₂, _, _, _, _, _, ultra, measure, _, quotient⟩ :=
      (h.components χ o hχo).read_l hZF hω mx theory model hq nx hN U w ξ ℓ e numbers finite powers
        carrier ownerClosed fk image pred closed hξ length loc
    have eq : c₁ = c₀ := Subtype.ext
      ((show Rr_finite_d I ω L N T z χ c₁.val from ⟨i, l'.val, hi, fχ, hil, fnχ, grχ⟩).unique_l
        hZF numbers hN.1 codeC)
    subst c₁
    have eq := fc'.domain_eq_l hN.1 fc
    subst l'
    have eq := actual.measures.function c₀ μ' μ hcμ' hcμ
    subst μ'
    obtain ⟨D₀, E₀, t₀, f₁, coord₀, pull₀, value₀⟩ := h.reindex_l hZF diagram limit hχJ edge₀ fv
    obtain ⟨Q₀, E₁, t₁, g₁, coord₁, pull₁, value₁⟩ := h.reindex_l hZF diagram limit hχJ edge₁ gv
    obtain ⟨ec₀, σ', p₀, f', F', fs', factor₀, fp₀, ps₀, comp₀, fF', graphF', valueF'⟩ :=
      coord₀.pull_l hZF numbers hN ξ ℓ m l a' c₀ d d₂ β f codeA codeC fa fc ds space ff dc fk.1 fF grF cf pull₀
    obtain ⟨ec₁, τ', p₁, g', G', ft', factor₁, fp₁, ps₁, comp₁, fG', graphG', valueG'⟩ :=
      coord₁.pull_l hZF numbers hN ξ ℓ n l b' c₀ d₁ d₂ β g codeB codeC fb fc qs space fg qc fk.1 fG grG cg pull₁
    have eq := hZF.1.eq_of_same_members E₀ D₂ (fun x => (ec₀ x).trans (dc₂ x).symm)
    subst E₀
    have eq := hZF.1.eq_of_same_members E₁ D₂ (fun x => (ec₁ x).trans (dc₂ x).symm)
    subst E₁
    have eq := ec_factor_unique_l hN.1 nativeInj fs' fσ factor₀ fσa
    subst σ'
    have eq := ec_factor_unique_l hN.1 nativeInj ft' fτ factor₁ fτb
    subst τ'
    have bounded := (actual.measures.at_l hN.1 hcμ fc space).1.1
    have nativeRel : Rp_rel_d (kp_pair_l hN) β μ R₀ f' g' :=
      ⟨B₀, hBμ, fun s hs => (eb_point_pull_l hN nativeFinite hm hn ds qs fp₀ fp₁ ff fg
        ps₀ ps₁ comp₀ comp₁ (bounded B₀ hBμ s hs)).mp (point s hs)⟩
    have cross := rr_cross_relation_l hZF nx hN d₂ β μ R₀ f' g' member comp₀.1 comp₁.1
      bounded dc₂ fi₂ id₂ measure fk pred fF' fG' graphF' graphG' valueF' valueG'
    exact (h.repr_atoms_l hZF diagram limit hχo quotient ultra.base value₀ value₁).2.mpr (cross.mp nativeRel)
  · intro edge
    obtain ⟨u, B₀, pu, hfB₀, huE⟩ := fv
    obtain ⟨v, B₁, pv, hgB₁, hvH⟩ := gv
    obtain ⟨χ, x, y, hxχ, hyχ, hux, hvy, hxy⟩ := (limit.relation u v E H₀ huE hvH).mp edge
    obtain ⟨P, px, o, C₁, W₁, hχo, pair, hPC⟩ := h.label_l hxχ
    obtain ⟨Q₁, py, atQ⟩ := h.label_l hyχ
    have hQC := (ep_at_read_l table hχo pair).mp atQ
    have rel := (ep_rel_read_l table hχo pair).mp ((h.relation_l px py).mp hxy).2.2
    obtain ⟨i, l, c₀, d₂, μ, hi, fχ, hil, fnχ, grχ, fc, space, _, hcμ,
      D₂, i₂, t₂, d₂', P₂, U₂, G₂, p₂, C₂, W₂, dc₂, fi₂, id₂, _, _, _, _, _, ultra, measure, _, quotient⟩ :=
      (h.components χ o hχo).read_l hZF hω mx theory model hq nx hN U w ξ ℓ e numbers finite powers
        carrier ownerClosed fk image pred closed hξ length loc
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair quotient.code.1
    have codeC : Rr_finite_d I ω L N T z χ c₀.val := ⟨i, l.val, hi, fχ, hil, fnχ, grχ⟩
    have hl : N₀.mem l w := (numbers.image l.val).mpr ⟨i, hi, hil⟩
    obtain ⟨_, _, _, inj⟩ := (h.indices χ).mp (h.projection.bound_l hxχ).2
    have nativeInj := (numbers.function_injective_l hZF hN.1 l ℓ c₀ hil fc
      (fχ.mono_target_l (fun x hx => ((length x).mp hx).1)) grχ).mp inj
    have hc₀ := (indices c₀).mpr ⟨l, hl, fc, nativeInj⟩
    obtain ⟨D₀, E₀, t₀, f₁, coord₀, hfP, pull₀⟩ := h.lift_l hZF.1 pu px hux hfB₀
    obtain ⟨Q₀, E₁, t₁, g₁, coord₁, hgQ, pull₁⟩ := h.lift_l hZF.1 pv py hvy hgB₁
    obtain ⟨ec₀, σ, p₀, f', F', fσ, factor₀, fp₀, ps₀, comp₀, fF', graphF', valueF'⟩ :=
      coord₀.pull_l hZF numbers hN ξ ℓ m l a' c₀ d d₂ β f codeA codeC fa fc ds space ff dc fk.1 fF grF cf pull₀
    obtain ⟨ec₁, τ, p₁, g', G', fτ, factor₁, fp₁, ps₁, comp₁, fG', graphG', valueG'⟩ :=
      coord₁.pull_l hZF numbers hN ξ ℓ n l b' c₀ d₁ d₂ β g codeB codeC fb fc qs space fg qc fk.1 fG grG cg pull₁
    have eq := hZF.1.eq_of_same_members E₀ D₂ (fun x => (ec₀ x).trans (dc₂ x).symm)
    subst E₀
    have eq := hZF.1.eq_of_same_members E₁ D₂ (fun x => (ec₁ x).trans (dc₂ x).symm)
    subst E₁
    have bounded := (actual.measures.at_l hN.1 hcμ fc space).1.1
    have point := (quotient.relation f₁ g₁ P Q₁
      (quotient.map.member_l I hZF.1 ultra.base hPC hfP) (quotient.map.member_l I hZF.1 ultra.base hQC hgQ)).mp rel
    obtain ⟨B, hB, point⟩ := (rr_cross_relation_l hZF nx hN d₂ β μ R₀ f' g' member comp₀.1 comp₁.1
      bounded dc₂ fi₂ id₂ measure fk pred fF' fG' graphF' graphG' valueF' valueG').mpr point
    have below x (hx : N₀.mem x l) : N₀.mem x ξ :=
      actual.critical.1.transitive l (actual.critical.1.transitive w actual.uncountable l hl) x hx
    have hσ := (nativeFinite σ).mpr ⟨m, hm, fn0_function_l hN (fσ.mono_target_l below)⟩
    have hτ := (nativeFinite τ).mpr ⟨n, hn, fn0_function_l hN (fτ.mono_target_l below)⟩
    exact ⟨c₀, hc₀, μ, measures c₀ μ hcμ, hcμ, B, hB,
      m, hm, n, hn, l, hl, σ, hσ, τ, hτ, fσ, fτ, fc, factor₀, factor₁,
      fun s hs => (eb_point_pull_l hN nativeFinite hm hn ds qs fp₀ fp₁ ff fg ps₀ ps₁
        comp₀ comp₁ (bounded B hB s hs)).mpr (point s hs)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原有界池在对象码极限中的完整实现

只使用原证书中的池与坍塌。原节点的求值由固定公式一次替换产生，
其关系与新极限完全相同，像覆盖常值像的全部成员和逐点前驱。所属结构只需 KP；
源内函数的完备性由原有限列空间和同一份实际极限秩历史直接证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

/-- 同一原池的坍塌值与原极限值确定完整实现图。 -/
def Er_present_d (I : kpair_convention_l.Interpretation M)
    (ω L N T z Γ Y k r e D t : M.Domain) : Prop := ∀ x E,
  Rd_entry_d x E t ↔ ∃ u, M.mem u D ∧ Rf_val_d I N T u x e ∧ Er_eval_d I ω L N T z Γ Y k r u E

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.raw_present_l {ω c' Y S Γ H k N T z L J O Z A p V W r o C W'
    b j H₁ D₀ a₀ f₀ : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (nx : ∃ x, M.mem x N) (hN : (smdl_structure_l I (R := T) nx).Models KP)
    (U w ξ ℓ e : (smdl_structure_l I (R := T) nx).Domain)
    (numbers : Rr_layer_d I ω N T w.val z) (finite : Fs_read_d w U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (ownerClosed : Rr_closed_d I N T U.val) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (closed : Rr_closed_d I Y S H) (hξ : (smdl_structure_l I (R := T) nx).mem ξ U)
    (length : ∀ x, M.mem x L ↔ M.mem x N ∧ Rd_entry_d x ℓ.val T)
    (β X₀ K₀ δ A' Q' Z' e' : (smdl_structure_l I (R := T) nx).Domain)
    (products : ∀ m d : (smdl_structure_l I (R := T) nx).Domain,
      (smdl_structure_l I (R := T) nx).mem m w → Ep_space_d ξ m d →
      ∃ P : (smdl_structure_l I (R := T) nx).Domain, (smdl_structure_l I (R := T) nx).mem P U ∧
        (smdl_structure_l I (R := T) nx).IsCartesianProduct (kp_pair_l hN) P d β)
    (sequences : Fseq_space_d (kp_pair_l hN) w ξ K₀)
    (hK : (smdl_structure_l I (R := T) nx).mem K₀ X₀)
    (rank : V_d (kp_pair_l hN) δ X₀)
    (height : (smdl_structure_l I (R := T) nx).IsLimitOrdinal δ)
    (hβ : (smdl_structure_l I (R := T) nx).mem β X₀)
    (trans : (smdl_structure_l I (R := T) nx).TransitiveSet β)
    (owned : Eb_collapse_d w ξ ℓ K₀ X₀ β e A' Q' Z' e')
    (h : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (diagram : Di_system_d J O A p V W) (limit : Di_limit_d A p V W r C W')
    (next : Smdl_d I o C W') (embed : Smap_d I ω c' o Y C j)
    (hβb : Rd_entry_d β.val b k) (hbH : Rd_entry_d b H₁ j)
    (ff₀ : Fn0_d D₀ Y f₀) (constant : Rs_const_d D₀ b f₀) (fv : Ep_repr_d r a₀ f₀ H₁)
    (loc : It_local_d I w.val N T ξ.val ℓ.val e.val) :
    ∃ D₁ Γ₁ s v t,
      (∀ u, M.mem u D₁ ↔ M.mem u N ∧ Rd_entry_d u A'.val T) ∧
      (∀ x, M.mem x Γ₁ ↔ M.mem x N ∧ Rd_entry_d x Z'.val T) ∧ Fn0_d D₁ Γ₁ s ∧
      (∀ u x : (smdl_structure_l I (R := T) nx).Domain, Rd_entry_d u.val x.val s ↔ Rd_entry_d u x e') ∧
      Fn0_d D₁ C v ∧
      (∀ u E, Rd_entry_d u E v ↔ M.mem u D₁ ∧ Er_eval_d I ω L N T z Γ Y k r u E) ∧
      (∀ u : (smdl_structure_l I (R := T) nx).Domain, (smdl_structure_l I (R := T) nx).mem u A' →
        ∃ α, ∃ m a d f : (smdl_structure_l I (R := T) nx).Domain,
          Ei_d ω L α ∧ Rr_finite_d I ω L N T z α a.val ∧
          (smdl_structure_l I (R := T) nx).mem m w ∧ Fn0_d m ℓ a ∧ Ep_space_d ξ m d ∧
          (smdl_structure_l I (R := T) nx).mem f U ∧ Fn0_d d β f ∧
          KPair_d (smdl_structure_l I (R := T) nx) u a f) ∧
      (∀ u x : (smdl_structure_l I (R := T) nx).Domain, ∀ E P,
        Rd_entry_d u.val E v → Rd_entry_d x.val P v → (Rd_entry_d u x Q' ↔ Rd_entry_d E P W')) ∧
      (∀ E, (∃ u, M.mem u D₁ ∧ Rd_entry_d u E v) ↔ Rd_entry_d E H₁ W') ∧
      M.IsSetInjectionFromTo I t Γ₁ C ∧
      Er_present_d I ω L N T z Γ Y k r e'.val D₁ t ∧
      (∀ E, Rd_entry_d E H₁ W' ↔ ∃ x, M.mem x Γ₁ ∧ Rd_entry_d x E t) ∧
      (∀ x E, Rd_entry_d x E t → ∀ P, Rd_entry_d P E W' ↔ ∃ y, Rd_entry_d y x T ∧ Rd_entry_d y P t) ∧
      ∀ x y : (smdl_structure_l I (R := T) nx).Domain, ∀ v E a D f,
        Eb_const_d X₀ β A' e' x y → Rd_entry_d x.val v k → Fn0_d D Y f →
          Rs_const_d D v f → Ep_repr_d r a f E → Rd_entry_d y.val E t := by
  let N₀ := smdl_structure_l I (R := T) nx
  let KpN := kp_pair_l hN
  obtain ⟨q, identity, _⟩ := smap_identity_l I hZF (X := Y) (c := c') hω
  have data := owned
  obtain ⟨Jn, Pn, Gn, Un, Rn, pool, indices, _, _, _, _, range, member, _, edges, collapse, reflect⟩ := data
  obtain ⟨D₁, Γ₁, s, ca, cz, sf, sr⟩ := smdl_graph_l hZF nx hN.1 A' Z' e' collapse.function
  obtain ⟨_, table⟩ := h.codes
  have key := fn0_of_function_l (ZF.modelsKP hZF) fk.1
  have space_mem m d (hm : N₀.mem m w) (ds : Ep_space_d ξ m d) : N₀.mem d X₀ :=
    v_subset_mem_l KpN rank hK (fun s hs => (sequences s).mpr
      ⟨m, hm, fn0_function_l hN ((ds s).mp hs)⟩)
  have powers (m d : N₀.Domain) (hm : N₀.mem m w) (ds : Ep_space_d ξ m d) :
      ∃ P, N₀.IsPowerSetOf P d := v_power_exists_l KpN hN rank (space_mem m d hm ds)
  have complete m d f (hm : N₀.mem m w) (ds : Ep_space_d ξ m d) (ff : Fn0_d d β f) : N₀.mem f X₀ := by
    obtain ⟨B, hB, hdB, hβB⟩ := v_joint_bound_l KpN rank (space_mem m d hm ds) hβ
    exact v_relation_mem_l KpN rank height hB (fun x hx => by
      obtain ⟨s, hs, y, hy, pair⟩ := ff.1 x hx
      exact ⟨s, hdB s hs, y, hβB y hy, pair⟩)
  have prepare (u : N₀.Domain) (hu : N₀.mem u A') :
      ∃ α, ∃ m α' d f : N₀.Domain, Ei_d ω L α ∧ Rr_finite_d I ω L N T z α α'.val ∧
        N₀.mem m w ∧ Fn0_d m ℓ α' ∧ Ep_space_d ξ m d ∧ N₀.mem f U ∧ Fn0_d d β f ∧ KPair_d N₀ u α' f := by
    obtain ⟨m, α', d, f, hm, hα, fa, ds, _, ff, pair⟩ := pool.read_l hN sequences hu
    obtain ⟨P, hP, product⟩ := products m d hm ds
    have hf := ownerClosed P.val f.val P.property f.property hP
      (fun x hx hxf => (product (⟨x, hx⟩ : N₀.Domain)).mpr (ff.1 ⟨x, hx⟩ hxf))
    obtain ⟨α, index, code⟩ := er_index_decode_l hZF numbers hN.1 ℓ α' length ((indices α').mp hα)
    exact ⟨α, m, α', d, f, index, code, hm, fa, ds, hf, ff, pair⟩
  let η : Env M 9 := ⟨Fin.cases r (Fin.cases k (Fin.cases Y (Fin.cases Γ (Fin.cases z
    (Fin.cases T (Fin.cases N (Fin.cases L (fun _ => ω)))))))), fun _ => N⟩
  let φ : BinarySchema 9 := {
    body := er_eval_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat u E : φ.denote η u E ↔ Er_eval_d I ω L N T z Γ Y k r u E := er_eval_sat_l I hZF.1 ..
  have total u (hu : M.mem u D₁) : ∃ E, φ.denote η u E := by
    let u' : N₀.Domain := ⟨u, ((ca u).mp hu).1⟩
    obtain ⟨α, m, α', d, f, index, code, _, fa, ds, hf, ff, pair⟩ := prepare u' ((ca u).mp hu).2
    obtain ⟨D, F, g, E, dc, fF, graph, comp, value, _⟩ := h.bounded_value_l hZF hω model ext theory
      nx hN U w ξ ℓ e β numbers finite powers carrier ownerClosed fk image pred closed hξ length limit hβb
      m α' d f ((h.indices α).mpr index) code fa ds hf ff loc
    exact ⟨E, (sat u E).mpr (Er_eval_d.write_l hZF nx hN.1 u' α' f d β code ff pair dc fF graph comp value)⟩
  have unique u (hu : M.mem u D₁) E P (he : φ.denote η u E) (hp : φ.denote η u P) : E = P := by
    let u' : N₀.Domain := ⟨u, ((ca u).mp hu).1⟩
    obtain ⟨α, m, α', d, f, index, code, _, fa, ds, _, ff, pair⟩ := prepare u' ((ca u).mp hu).2
    obtain ⟨D, F, g, dc, fF, graph, comp, value⟩ := ((sat u E).mp he).read_l hZF numbers hN.1 u' α' f d β code ff pair
    obtain ⟨D', F', g', dc', fF', graph', comp', value'⟩ := ((sat u P).mp hp).read_l hZF numbers hN.1 u' α' f d β code ff pair
    have eq := hZF.1.eq_of_same_members D' D (fun x => (dc' x).trans (dc x).symm)
    subst D'
    have eq := fF'.ext_l hZF.1 fF (fun s hs => by
      obtain ⟨v, hv, hsv⟩ := fF'.2.1 s hs
      let s' : N₀.Domain := ⟨s, ((dc s).mp hs).1⟩
      let v' : N₀.Domain := ⟨v, ((carrier v).mp hv).1⟩
      exact ⟨v, hsv, (graph s' v').mpr ((graph' s' v').mp hsv)⟩)
    subst F'
    have eq := cp0_unique_l hZF.1 fF key comp' comp
    subst g'
    obtain ⟨o₀, _, hαo⟩ := table.2.1 α ((h.indices α).mpr index)
    obtain ⟨i, m₀, α₀, d₀, _, hi, fα, him, fnα, grα, fa₀, ds₀, _, _,
      D₂, _, _, _, _, U₂, G₂, p₂, C₂, W₂, dc₂, _, _, _, _, _, _, _, ultra, _, _, quotient⟩ :=
      (h.components α o₀ hαo).read_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers
        carrier ownerClosed fk image pred closed hξ length loc
    have eq : α₀ = α' := Subtype.ext
      ((show Rr_finite_d I ω L N T z α α₀.val from ⟨i, m₀.val, hi, fα, him, fnα, grα⟩).unique_l
        hZF numbers hN.1 code)
    subst α₀
    have eq := fa₀.domain_eq_l hN.1 fa
    subst m₀
    have eq := hN.1.eq_of_same_members d₀ d (fun x => (ds₀ x).trans (ds x).symm)
    subst d₀
    have eq := hZF.1.eq_of_same_members D₂ D (fun x => (dc₂ x).trans (dc x).symm)
    subst D₂
    exact (h.repr_atoms_l hZF diagram limit hαo quotient ultra.base value value').1.mpr (rp_eq_refl_l ultra.base comp.1)
  obtain ⟨v, vf, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ η total unique (fun u E _ he => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, x, B, pair, hg, hxE⟩ := (sat u E).mp he
    exact (limit.projection.bound_l hxE).2)
  have values u E : Rd_entry_d u E v ↔ M.mem u D₁ ∧ Er_eval_d I ω L N T z Γ Y k r u E :=
    (spec u E).trans (and_congr Iff.rfl (sat u E))
  have entry (u : N₀.Domain) E (huE : Rd_entry_d u.val E v) :
      ∃ α, ∃ m α' d f : N₀.Domain, ∃ D F g,
        N₀.mem m w ∧ M.mem α J ∧ Rr_finite_d I ω L N T z α α'.val ∧ Fn0_d m ℓ α' ∧ Ep_space_d ξ m d ∧
        Fn0_d d β f ∧ (∀ s, M.mem s D ↔ M.mem s N ∧ Rd_entry_d s d.val T) ∧ Fn0_d D Γ F ∧
        (∀ s v : N₀.Domain, Rd_entry_d s.val v.val F ↔ Rd_entry_d s v f) ∧ Cp0_d D Γ Y F k g ∧
        Ep_repr_d r α g E ∧ KPair_d N₀ u α' f := by
    obtain ⟨hu, value⟩ := (values u.val E).mp huE
    obtain ⟨α, m, α', d, f, index, code, hm, fa, ds, _, ff, pair⟩ := prepare u ((ca u.val).mp hu).2
    obtain ⟨D, F, g, dc, fF, graph, comp, ev⟩ := value.read_l hZF numbers hN.1 u α' f d β code ff pair
    exact ⟨α, m, α', d, f, D, F, g, hm, (h.indices α).mpr index, code, fa, ds, ff, dc, fF, graph, comp, ev, pair⟩
  have relation (u z' : N₀.Domain) E P (huE : Rd_entry_d u.val E v) (hzP : Rd_entry_d z'.val P v) :
      Rd_entry_d u z' Q' ↔ Rd_entry_d E P W' := by
    obtain ⟨α, m, α', d, f, D, F, g, hm, _, codeA, fa, ds, ff, dc, fF, grF, cf, fv', pu⟩ := entry u E huE
    obtain ⟨γ, n, γ', d', f', Q, G, g', hn, _, codeB, fb, qs, fg, qc, fG, grG, cg, gv', pv⟩ := entry z' P hzP
    have hu := ((ca u.val).mp (vf.input_mem_of_pairMember huE)).2
    have hz := ((ca z'.val).mp (vf.input_mem_of_pairMember hzP)).2
    obtain ⟨a₁, ha₁, f₁, hf₁, pu₁, _⟩ := (pool.nodes u).mp hu
    obtain ⟨b₁, hb₁, g₁, hg₁, pv₁, _⟩ := (pool.nodes z').mp hz
    obtain ⟨rfl, rfl⟩ := kpair_injective_l N₀ pu pu₁
    obtain ⟨rfl, rfl⟩ := kpair_injective_l N₀ pv pv₁
    have links : Eb_link_d w ξ ℓ β Jn K₀ Un Rn e Gn u z' ↔ Eb_edge_d w ξ ℓ β Jn K₀ Un Rn e α' f γ' f' := by
      refine ⟨?_, fun edge => ⟨α', ha₁, f, hf₁, γ', hb₁, f', hg₁, pu, pv, edge⟩⟩
      rintro ⟨a, _, f₀, _, b, _, g₀, _, pa, pb, edge⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l N₀ pa pu
      obtain ⟨rfl, rfl⟩ := kpair_injective_l N₀ pb pv
      exact edge
    exact (edges u z').trans ((and_iff_right hu).trans ((and_iff_right hz).trans (links.trans
      (loc.code_edge_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers carrier ownerClosed fk image pred
        closed hξ length m n α' γ' d d' β Jn K₀ Un Rn f f' indices sequences
        (fun a μ haμ => (range μ).mpr ⟨a, haμ⟩) member hm hn codeA codeB fa fb ds qs ff fg dc qc
        fF fG grF grG cf cg h diagram limit fv' gv'))))
  have covers E : (∃ u, M.mem u D₁ ∧ Rd_entry_d u E v) ↔ Rd_entry_d E H₁ W' := by
    constructor
    · rintro ⟨u, hu, huE⟩
      obtain ⟨α, m, α', d, f, D, F, g, _, _, _, _, _, ff, dc, fF, graph, comp, value, _⟩ :=
        entry ⟨u, ((ca u).mp hu).1⟩ E huE
      apply h.bound_mem_l hZF hω model theory model identity nx hN U w ξ ℓ e numbers finite powers carrier ownerClosed
        fk image pred closed hξ length diagram limit (fk.1.output_mem_of_pairMember hβb) ff₀ constant fv (g := g) ?_ value loc
      intro s y hsy
      let s' : N₀.Domain := ⟨s, ((dc s).mp (comp.1.bound_l hsy).1).1⟩
      obtain ⟨x, hx, hsx⟩ := ff.2.1 s' ((dc s).mp (comp.1.bound_l hsy).1).2
      exact (pred β.val b hβb y).mpr ⟨x.val, hx, (comp.value_l fF key ((graph s' x).mpr hsx)).mp hsy⟩
    · intro edge
      obtain ⟨α, m, α', d, f, D, F, g, hαJ, code, hm, fa, ds, _, ff, dc, fF, graph, comp, value⟩ :=
        h.bounded_l hZF hω model ext theory nx hN U w ξ ℓ e β numbers finite powers carrier ownerClosed fk image pred
          closed hξ length products diagram limit hβb ff₀ constant fv edge loc
      have data := code
      obtain ⟨i, m₀, _, fα, him, fnα, grα⟩ := data
      let m' : N₀.Domain := ⟨m₀, numbers.injection.1.output_mem_of_pairMember him⟩
      obtain ⟨B, fm⟩ := (rf_fun_native_l I nx hN.1 m' α').mp fnα
      have eq : m₀ = m.val := congrArg (fun x : N₀.Domain => x.val) (fm.domain_eq_l hN.1 fa)
      have him : Rd_entry_d i m.val z := eq ▸ him
      obtain ⟨_, _, _, inj⟩ := (h.indices α).mp hαJ
      have inj' := (numbers.function_injective_l hZF hN.1 m ℓ α' him fa
        (fα.mono_target_l (fun x hx => ((length x).mp hx).1)) grα).mp inj
      have hα := (indices α').mpr ⟨m, hm, fa, inj'⟩
      obtain ⟨u, pair⟩ := KpN.total α' f
      have hu := pool.node_l hN sequences hm hα fa ds (space_mem m d hm ds) (complete m d f hm ds ff) ff pair
      have huD := (ca u.val).mpr ⟨u.property, hu⟩
      exact ⟨u.val, huD, (values u.val E).mpr ⟨huD, Er_eval_d.write_l hZF nx hN.1 u α' f d β code ff pair dc fF graph comp value⟩⟩
  have nextExt := embed.extensional_l hZF hω model next ext
  have hβU : N₀.mem β U := ((carrier β.val).mp (fk.1.input_mem_of_pairMember hβb)).2
  let nu : Nonempty {x : N₀.Domain // N₀.mem x U} := ⟨⟨β, hβU⟩⟩
  let ρ : Env (rt_model_l U nu) 1 := ⟨fun _ => ⟨β, hβU⟩, fun _ => ⟨β, hβU⟩⟩
  let τ : Env (smdl_structure_l I (R := S) model.2.1) 1 :=
    ⟨fun _ => ⟨b, fk.1.output_mem_of_pairMember hβb⟩, fun _ => ⟨b, fk.1.output_mem_of_pairMember hβb⟩⟩
  let σ : Env (smdl_structure_l I (R := W') next.2.1) 1 :=
    ⟨fun _ => ⟨H₁, embed.1.1.output_mem_of_pairMember hbH⟩, fun _ => ⟨H₁, embed.1.1.output_mem_of_pairMember hbH⟩⟩
  have oldTrans := (rr_native_delta_l I nx model.2.1 U finite.transitive nu carrier fk pred
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _) ρ τ (fun _ => hβb)).mp
      ((Formula.satisfies_isTransitive_iff ..).mpr trans)
  have newTrans := (Formula.satisfies_isTransitive_iff ..).mp
    ((smap_source_l I hZF hω model next embed (Formula.isTransitive .newest) (by simp -implicitDefEqProofs)
      τ σ (fun _ => hbH)).mp oldTrans)
  let left x y := M.mem x N ∧ Rd_entry_d x y T
  have leftExt x (hx : M.mem x Γ₁) y (hy : M.mem y Γ₁)
      (same : ∀ z, M.mem z Γ₁ → (left z x ↔ left z y)) : x = y := by
    suffices eq : (⟨x, ((cz x).mp hx).1⟩ : N₀.Domain) = ⟨y, ((cz y).mp hy).1⟩ from congrArg Subtype.val eq
    apply hN.1.eq_of_same_members (⟨x, ((cz x).mp hx).1⟩ : N₀.Domain) ⟨y, ((cz y).mp hy).1⟩
    intro z
    exact ⟨fun hz => ((same z.val ((cz z.val).mpr ⟨z.property,
      collapse.transitive ⟨x, ((cz x).mp hx).1⟩ ((cz x).mp hx).2 z hz⟩)).mp ⟨z.property, hz⟩).2,
      fun hz => ((same z.val ((cz z.val).mpr ⟨z.property,
        collapse.transitive ⟨y, ((cz y).mp hy).1⟩ ((cz y).mp hy).2 z hz⟩)).mpr ⟨z.property, hz⟩).2⟩
  have onto x (hx : M.mem x Γ₁) : ∃ u, M.mem u D₁ ∧ Rd_entry_d u x s := by
    let x' : N₀.Domain := ⟨x, ((cz x).mp hx).1⟩
    obtain ⟨u, hu, hux⟩ := collapse.onto x' ((cz x).mp hx).2
    exact ⟨u.val, (ca u.val).mpr ⟨u.property, hu⟩, (sr u x').mpr hux⟩
  have leftCover u x (hux : Rd_entry_d u x s) y (hy : left y x) : ∃ z, M.mem z D₁ ∧ Rd_entry_d z y s := by
    have hx := (cz x).mp (sf.bound_l hux).2
    exact onto y ((cz y).mpr ⟨hy.1, collapse.transitive ⟨x, hx.1⟩ hx.2 ⟨y, hy.1⟩ hy.2⟩)
  have leftExact u z' x y (hux : Rd_entry_d u x s) (hzy : Rd_entry_d z' y s) :
      Rf_val_d I N T u z' Q'.val ↔ left x y := by
    let u' : N₀.Domain := ⟨u, ((ca u).mp (sf.bound_l hux).1).1⟩
    let z'' : N₀.Domain := ⟨z', ((ca z').mp (sf.bound_l hzy).1).1⟩
    let x' : N₀.Domain := ⟨x, ((cz x).mp (sf.bound_l hux).2).1⟩
    let y' : N₀.Domain := ⟨y, ((cz y).mp (sf.bound_l hzy).2).1⟩
    exact (rf_val_native_l I nx hN.1 u' z'' Q').trans
      ((reflect u' z'' x' y' ((sr u' x').mp hux) ((sr z'' y').mp hzy)).trans ((and_iff_right x'.property).symm))
  have relation' u z' E P (hu : Rd_entry_d u E v) (hz : Rd_entry_d z' P v) :
      Rf_val_d I N T u z' Q'.val ↔ Rd_entry_d E P W' :=
    (rf_val_native_l I nx hN.1 ⟨u, ((ca u).mp (vf.input_mem_of_pairMember hu)).1⟩
      ⟨z', ((ca z').mp (vf.input_mem_of_pairMember hz)).1⟩ Q').trans (relation _ _ E P hu hz)
  obtain ⟨t, ft, graph, _, predecessors⟩ := rr_span_realize_l hZF left sf onto leftExt leftExact leftCover
    (fn0_of_function_l (ZF.modelsKP hZF) vf) nextExt relation' (fun u E huE P hPE => (covers P).mpr
      (newTrans ⟨E, vf.output_mem_of_pairMember huE⟩ ((covers E).mp ⟨u, vf.input_mem_of_pairMember huE, huE⟩)
        ⟨P, (limit.bounded P E hPE).1⟩ hPE))
  refine ⟨D₁, Γ₁, s, v, t, ca, cz, sf, sr, fn0_of_function_l (ZF.modelsKP hZF) vf,
    values, prepare, relation, covers, ft, ?_, fun E => ?_, fun x E hx P => ?_, ?_⟩
  · intro x E
    constructor
    · intro hxE
      obtain ⟨u, hu, hux, huE⟩ := (graph x E).mp hxE
      let u' : N₀.Domain := ⟨u, ((ca u).mp hu).1⟩
      let x' : N₀.Domain := ⟨x, ((cz x).mp (sf.bound_l hux).2).1⟩
      exact ⟨u, hu, (rf_val_native_l I nx hN.1 u' x' e').mpr ((sr u' x').mp hux), ((values u E).mp huE).2⟩
    · rintro ⟨u, hu, hux, value⟩
      let u' : N₀.Domain := ⟨u, ((ca u).mp hu).1⟩
      let x' : N₀.Domain := ⟨x, (hux.bounds_l I).2.1⟩
      exact (graph x E).mpr ⟨u, hu, (sr u' x').mpr ((rf_val_native_l I nx hN.1 u' x' e').mp hux),
        (values u E).mpr ⟨hu, value⟩⟩
  · refine (covers E).symm.trans ⟨?_, ?_⟩
    · rintro ⟨u, hu, huE⟩
      obtain ⟨x, hx, hux⟩ := sf.2.1 u hu
      exact ⟨x, hx, (graph x E).mpr ⟨u, hu, hux, huE⟩⟩
    · rintro ⟨x, _, hxE⟩
      obtain ⟨u, hu, _, huE⟩ := (graph x E).mp hxE
      exact ⟨u, hu, huE⟩
  · exact (predecessors x E hx P).trans ⟨fun ⟨y, hy, hyP⟩ => ⟨y, hy.2, hyP⟩,
      fun ⟨y, hy, hyP⟩ => ⟨y, ⟨((cz y).mp (ft.1.input_mem_of_pairMember hyP)).1, hy⟩, hyP⟩⟩
  · intro x y b E a D f old hxb ff fc fv
    obtain ⟨u, hu, a₁, _, f₁, _, d₁, _, pair₁, fn₁, constant₁, huy⟩ := old
    have huD := (ca u.val).mpr ⟨u.property, hu⟩
    obtain ⟨E₀, _, huE⟩ := vf.2.2 u.val huD
    have hyE := (graph y.val E₀).mpr ⟨u.val, huD, (sr u y).mpr huy, huE⟩
    obtain ⟨α, m, a₂, d₂, f₂, D₂, F₂, g₂, _, _, _, _, _, fn₂, dc, fF, grF, comp, ev, pair₂⟩ := entry u E₀ huE
    have feq := (kpair_injective_l N₀ pair₂ pair₁).2
    have deq := (feq ▸ fn₂).domain_eq_l hN.1 fn₁
    have cg : Rs_const_d D₂ b g₂ := by
      intro s hs
      let s' : N₀.Domain := ⟨s, ((dc s).mp hs).1⟩
      have value : Rd_entry_d s' x f₂ := feq.symm ▸ constant₁ s' (deq ▸ ((dc s).mp hs).2)
      exact (comp.value_l fF key ((grF s' x).mpr value)).mpr hxb
    exact (h.constant_l hZF nx KpN hN.1 w ξ ℓ e numbers length loc diagram limit comp.1 ff cg fc ev fv) ▸ hyE

end YesMetaZFC.SetTheory.LargeCardinal
