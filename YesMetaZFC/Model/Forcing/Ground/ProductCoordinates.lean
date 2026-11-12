import YesMetaZFC.Model.Forcing.Collapse.ProductCoordinates
import YesMetaZFC.Model.Forcing.Collapse.ProductReflection
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # 原泛型的实际坐标滤子列与全部有限前缀

每个坐标滤子由原泛型的行加强关系分离，替代将它们编码为同一背景函数图。
其任意有限限制恰好接受原 G 的对应前缀，保留原滤子与原条件，不另选泛型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}}

def Fp_coord_d (X P G i K : M.Domain) : Prop := ∀ a, M.mem a K ↔ M.mem a X ∧
  (∃ q, M.mem q P ∧ Rd_entry_d i a q) ∧
  ∃ p b, M.mem p G ∧ Rd_entry_d i b p ∧ M.MemberSubset a b

def fp_coord_m {d} (X P G i K : Term d) : Formula 1 d := set[d] ⟪
  ∀ a, a ∈ ⌜K⌝ₛ ↔ a ∈ ⌜X⌝ₛ ∧ (∃ q ∈ ⌜P⌝ₛ, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ,a,q)) ∧
    (∃ p ∈ ⌜G⌝ₛ, ∃ b, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ,b,p) ∧ a ⊆ b)⟫
derive_free_closed fp_coord_m

theorem fp_coord_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X P G i K : Term d) :
    Formula.satisfies ρ (fp_coord_m X P G i K) ↔
      Fp_coord_d (X.eval ρ) (P.eval ρ) (G.eval ρ) (i.eval ρ) (K.eval ρ) := by
  simp only [fp_coord_m,Fp_coord_d,Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_conj_iff,Formula.satisfies_existsMem_iff,
    Formula.satisfies_exists_iff,rd_entry0_sat_l hE,Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken]
  exact forall_congr' fun _ => iff_congr Iff.rfl (and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun ⟨p,hp,b,edge,sub⟩ => ⟨p,b,hp,edge,sub⟩,fun ⟨p,b,hp,edge,sub⟩ => ⟨p,hp,b,edge,sub⟩⟩)

variable (hM : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)

/-- 坐标滤子同时集合化；唯一成员方程使所有有限限制共用同一列。 -/
theorem fp_coords_l (X P G : M.Domain) {n : M.Domain} (on : M.IsOrdinal n) :
    ∃ F, M.IsSequenceOfLength I F n ∧
      ∀ i K, Rd_entry_d i K F ↔ M.mem i n ∧ Fp_coord_d X P G i K := by
  let ρ : Env M 3 := ⟨fun k => [X,P,G].get k,fun _ => X⟩
  let φ : BinarySchema 3 := { body := fp_coord_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have read i K : φ.denote ρ i K ↔ Fp_coord_d X P G i K := fp_coord_sat_l hM.1 ..
  have total i : ∃ K, φ.denote ρ i K := by
    let η : Env M 3 := ⟨fun k => [P,G,i].get k,fun _ => i⟩
    let ψ : UnarySchema 3 := { body := set[4] ⟪
      (∃ q ∈ ⌜(.bound 1 : Term 4)⌝ₛ, ⌜rd_entry0_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ,⌜(.newest : Term 4)⌝ₛ,q)) ∧
      (∃ p ∈ ⌜(.bound 2 : Term 4)⌝ₛ, ∃ b, ⌜rd_entry0_m⌝ₚ(⌜(.bound 3 : Term 4)⌝ₛ,b,p) ∧ ⌜(.newest : Term 4)⌝ₛ ⊆ b)⟫ }
    obtain ⟨K,members⟩ := ZF.separation_exists_d hM ψ η X
    refine ⟨K,(read i K).mpr (fun a => (members a).trans (and_congr_right fun _ => ?_))⟩
    simp only [ψ,Formula.satisfies_conj_iff,Formula.satisfies_existsMem_iff,
      Formula.satisfies_exists_iff,rd_entry0_sat_l hM.1,Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
    exact and_congr_right fun _ =>
      ⟨fun ⟨p,hp,b,edge,sub⟩ => ⟨p,b,hp,edge,sub⟩,fun ⟨p,b,hp,edge,sub⟩ => ⟨p,hp,b,edge,sub⟩⟩
  have unique i K L (hK : φ.denote ρ i K) (hL : φ.denote ρ i L) : K = L :=
    hM.1.eq_of_same_members K L (fun a => ((read i K).mp hK a).trans ((read i L).mp hL a).symm)
  obtain ⟨W,range⟩ := ZF.exists_functionalImage hM φ ρ n (fun i _ => total i) unique
  obtain ⟨F,fn,edges⟩ := ZF.exists_setFunctionFromTo_of_denote hM I φ ρ (fun i _ => total i)
    (fun i _ => unique i) (fun i K hi hK => (range K).mpr ⟨i,hi,hK⟩)
  exact ⟨F,⟨on,fn.1,fn.2.1⟩,fun i K => (edges i K).trans (and_congr_right fun _ => read i K)⟩

variable {c X R : M.Domain} (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R)
  (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
include trans

/-- 原全泛型的一个背景坐标列，同时产生所有原有限前缀及其实际泛型证书。 -/
theorem Smem_d.product_coordinates_l
    {ω A P T W : (smdl_structure_l I (R := R) source.1.2.1).Domain} {G : M.Domain}
    (hw : (smdl_structure_l I (R := R) source.1.2.1).IsOmega ω)
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP native)) A ω W)
    (product : Fp_product_d native ω A P T) (generic : Gset_d P.val T.val P.val X G) :
    ∃ F, M.IsSequenceOfLength I F ω.val ∧
      (∀ i K, Rd_entry_d i K F ↔ M.mem i ω.val ∧ Fp_coord_d X P.val G i K) ∧
      ∀ n C S : (smdl_structure_l I (R := R) source.1.2.1).Domain,
        (smdl_structure_l I (R := R) source.1.2.1).mem n ω → Fp_prefix_d native ω A n C S →
        ∃ f K, M.IsSequenceOfLength I f n.val ∧ M.IsRestrictionOf I f F n.val ∧
          Fp_filter_project_d C.val T.val G K ∧
          (∀ q, M.mem q K ↔ M.mem q C.val ∧ Fp_ready_d I n.val f q) ∧
          (∀ q, M.mem q G → Fp_ready_d I n.val f q) ∧
          Gset_d C.val S.val C.val X K := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : N.Domain} : N.mem a b ↔ M.mem a.val b.val :=
    (image_member_l (M := N) (N := M) Subtype.val inj full).symm
  have entry := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hM.1
  have endpoints {q i a} (hq : M.mem q X) (edge : Rd_entry_d i a q) : M.mem i X ∧ M.mem a X :=
    edge.choose_spec.1.mem_l M trans (trans q hq _ edge.choose_spec.2)
  have ordinal {a : N.Domain} (oa : N.IsOrdinal a) :=
    image_ord_l (M := N) (N := M) native hM Subtype.val inj full oa
  obtain ⟨F,seq,rows⟩ := fp_coords_l hM X P.val G (ordinal (hw.isOrdinal (ZF.modelsKP native)))
  obtain ⟨sub,g⟩ := (source.generic_code_l I hM.1 trans (ZF.modelsKP native) P T P G).mp generic
  refine ⟨F,seq,rows,?_⟩
  -- 所有有限列均取同一 F 的原限制，而非逐次选择互不相关的坐标泛型。
  intro n C S hn stage
  obtain ⟨f,cut⟩ := ZF.exists_restriction hM I F n.val
  have small : M.MemberSubset n.val ω.val :=
    (ordinal (hw.isOrdinal (ZF.modelsKP native))).transitive n.val (member.mp hn)
  have ff : M.IsSetFunction I f := ⟨cut.1,fun i a b ia ib =>
    seq.2.1.2 i a b ((cut.2 i a).mp ia).2 ((cut.2 i b).mp ib).2⟩
  have dom : M.IsDomainOf I n.val f := fun i =>
    ⟨fun hi => ((seq.2.2 i).mp (small i hi)).elim fun K edge => ⟨K,(cut.2 i K).mpr ⟨hi,edge⟩⟩,
      fun ⟨K,edge⟩ => ((cut.2 i K).mp edge).1⟩
  have coords i K : Rd_entry_d i K f ↔ M.mem i n.val ∧ Fp_coord_d X P.val G i K :=
    (cut.2 i K).trans ((and_congr_right fun _ => rows i K).trans
      ⟨fun ⟨hi,_,spec⟩ => ⟨hi,spec⟩,fun ⟨hi,spec⟩ => ⟨hi,small i hi,spec⟩⟩)
  obtain ⟨K,projection,gK⟩ := Smem_d.product_project_l hM source trans native hw hn fa product stage generic
  have read := Smem_d.project_filter_read_l hM source trans native product stage hn sub projection
  have frozen q (gq : M.mem q G) : Fp_ready_d I n.val f q := by
    intro i a hi ia
    obtain ⟨L,edge⟩ := (dom i).mp hi
    exact ⟨L,edge,(((coords i L).mp edge).2 a).mpr
      ⟨(endpoints (trans P.val P.property q (sub q gq)) ia).2,
        ⟨q,sub q gq,ia⟩,q,a,gq,ia,fun _ h => h⟩⟩
  have accepts (q : N.Domain) (hq : N.mem q C) : M.mem q.val G ↔ Fp_ready_d I n.val f q.val := by
    have qP := ((stage.product_read_l native product hn).1 q).mp hq |>.1
    constructor
    · exact frozen q.val
    · intro ready
      -- 地模型中的相容性判定恢复原 G；这里无需对外部 G 作内部归纳。
      apply (product.generic_rows_l native hw g qP).mpr
      intro i a ia
      have hi := ((stage.conditions q).mp hq).domain i |>.mpr ⟨a,ia⟩
      obtain ⟨L,edge,ha⟩ := ready i.val a.val (member.mp hi) ((entry i a q).mp ia)
      obtain ⟨_,_,p,b,gp,ib,ab⟩ := ((coords i.val L).mp edge).2 a.val |>.mp ha
      let p₀ : N.Domain := ⟨p,trans P.val P.property p (sub p gp)⟩
      let b₀ : N.Domain := ⟨b,(endpoints p₀.property ib).2⟩
      exact ⟨p₀,b₀,gp,(entry i b₀ p₀).mpr ib,fun z hz => member.mpr (ab z.val (member.mp hz))⟩
  refine ⟨f,K,⟨ordinal (hw.members_areOrdinals (ZF.modelsKP native) n hn),ff,dom⟩,cut,projection,?_,frozen,gK⟩
  intro q
  constructor
  · intro hq
    have qc := ((projection q).mp hq).1
    let q₀ : N.Domain := ⟨q,trans C.val C.property q qc⟩
    obtain ⟨hc,p,gp,pq⟩ := (read q₀).mp hq
    have qP := ((stage.product_read_l native product hn).1 q₀).mp hc |>.1
    have gq := g.upward p q₀ gp qP ((product.order p q₀).mpr ⟨(g.proper p gp).1,qP,pq⟩)
    exact ⟨qc,(accepts q₀ hc).mp gq⟩
  · rintro ⟨qc,ready⟩
    let q₀ : N.Domain := ⟨q,trans C.val C.property q qc⟩
    have hc : N.mem q₀ C := member.mpr qc
    exact (read q₀).mpr ⟨hc,q₀,(accepts q₀ hc).mpr ready,Fp_le_d.refl_l (kp_pair_l (ZF.modelsKP native)) q₀⟩

end YesMetaZFC.Model.Forcing.Internal
