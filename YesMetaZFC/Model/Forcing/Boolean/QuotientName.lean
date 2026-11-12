import YesMetaZFC.Model.Forcing.Boolean.QuotientProjection

/-! # 商条件集的实际首阶段名称

把旧目标条件 x 的规范名称赋以 π(x) 中的小条件作为权重。
成员力迫精确等于投影中的成员关系，因此此名称可直接充当二步迭代的第二坐标域。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

def Qname_d (Q c L d P τ : M.Domain) : Prop := Name_d M Q τ ∧
  ∀ t q, Entry_d M t q τ ↔ M.mem q Q ∧ ∃ x a,
    M.mem x L ∧ x ≠ d ∧ Check_d M c x t ∧ Entry_d M x a P ∧ M.mem q a

def qname_m {n} (Q c L d P τ : Term n) : Formula 1 n := set[n] ⟪
  ⌜name_m⌝ₚ(⌜Q⌝ₛ,⌜τ⌝ₛ) ∧ (∀ t, ∀ q, ⌜entry_m⌝ₚ(t,q,⌜τ⌝ₛ) ↔ q ∈ ⌜Q⌝ₛ ∧
    (∃ x ∈ ⌜L⌝ₛ, x ≠ ⌜d⌝ₛ ∧ (∃ a, ⌜check_m⌝ₚ(⌜c⌝ₛ,x,t) ∧ ⌜entry_m⌝ₚ(x,a,⌜P⌝ₛ) ∧ q ∈ a)))⟫
derive_free_closed qname_m

theorem qname_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Q c L d P τ : Term n) :
    Formula.satisfies ρ (qname_m Q c L d P τ) ↔
      Qname_d (Q.eval ρ) (c.eval ρ) (L.eval ρ) (d.eval ρ) (P.eval ρ) (τ.eval ρ) := by
  simp only [qname_m,Qname_d,Formula.satisfies_conj_iff,name_sat_l M hE,
    Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,entry_sat_l M hE,
    Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
    Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    check_sat_l M hE,Definitional.Term.eval_weaken]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  apply forall_congr'
  intro q
  apply iff_congr Iff.rfl
  apply and_congr_right
  intro _
  exact ⟨fun ⟨x,hx,nz,a,check,xa,qa⟩ => ⟨x,a,hx,nz,check,xa,qa⟩,
    fun ⟨x,a,hx,nz,check,xa,qa⟩ => ⟨x,hx,nz,a,check,xa,qa⟩⟩

include hZF

theorem qname_exists_l {Q c : M.Domain} (hc : M.mem c Q) (L d P : M.Domain) :
    ∃ τ, Qname_d Q c L d P τ := by
  obtain ⟨W,mem,names⟩ := check_image_l hZF hc L
  let ρ : Env M 4 := ⟨fun i => [c,L,d,P].get i,fun _ => c⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    ∃ x ∈ ⌜(.bound 3 : Term 6)⌝ₛ, x ≠ ⌜(.bound 4 : Term 6)⌝ₛ ∧ (∃ a,
      ⌜check_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ,x,⌜(.bound 1 : Term 6)⌝ₛ) ∧
      ⌜entry_m⌝ₚ(x,a,⌜(.bound 5 : Term 6)⌝ₛ) ∧ ⌜(.bound 0 : Term 6)⌝ₛ ∈ a)⟫ }
  have sat t q : φ.denote ρ t q ↔ ∃ x a, M.mem x L ∧ x ≠ d ∧
      Check_d M c x t ∧ Entry_d M x a P ∧ M.mem q a := by
    simp only [BinarySchema.denote,φ,Formula.satisfies_existsMem_iff,Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,check_sat_l M hZF.1,entry_sat_l M hZF.1,
      Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    exact ⟨fun ⟨x,hx,nz,a,check,xa,qa⟩ => ⟨x,a,hx,nz,check,xa,qa⟩,
      fun ⟨x,a,hx,nz,check,xa,qa⟩ => ⟨x,hx,nz,a,check,xa,qa⟩⟩
  obtain ⟨τ,name,_,graph⟩ := name_comp_l M hZF φ ρ Q W names
  refine ⟨τ,name,fun t q => (graph t q).trans ?_⟩
  constructor
  · rintro ⟨_,hq,h⟩
    exact ⟨hq,(sat t q).mp h⟩
  · rintro ⟨hq,x,a,hx,nz,check,xa,qa⟩
    exact ⟨(mem t).mpr ⟨x,hx,check⟩,hq,(sat t q).mpr ⟨x,a,hx,nz,check,xa,qa⟩⟩

theorem Qname_d.force_l {Q T w c L d A P τ x a t q : M.Domain} (O : Cond_order_d M Q T w)
    (hc : M.mem c Q) (fn : M.IsSetFunctionFromTo I P L A)
    (regular : ∀ a, M.mem a A → Ropen_d Q T w a) (name : Qname_d Q c L d P τ)
    (xa : Entry_d M x a P) (check : Check_d M c x t) (hq : Below_d M Q T w q c) :
    Mem_force_d M Q T w q t τ ↔ x ≠ d ∧ M.mem q a := by
  have ha := regular a (fn.output_mem_of_pairMember xa)
  constructor
  · intro force
    have match' r (hr : Below_d M Q T w r q) : ∃ s, Below_d M Q T w s r ∧ x ≠ d ∧ M.mem s a := by
      obtain ⟨s,v,p,hs,vp,sp,eq⟩ := force.2 r hr
      obtain ⟨hp,y,b,_,nz,check',yb,pb⟩ := (name.2 v p).mp vp
      have xy := check_force_reflect_l O hZF hc check check'
        (below_trans_l O hc hs (below_trans_l O hc hr hq)) eq
      subst y
      have ab := fn.1.2 x b a yb xa
      subst b
      exact ⟨s,hs,nz,ha.2.1 p s hp ⟨hs.1,hs.2.1,sp⟩ pb⟩
    obtain ⟨_,_,nz,_⟩ := match' q (below_refl_l O hq.1 hq.2.1)
    exact ⟨nz,ha.2.2 q hq.1 hq.2.1 (fun r hr => (match' r hr).imp fun s hs => ⟨hs.1,hs.2.2⟩)⟩
  · rintro ⟨nz,qa⟩
    exact mem_force_entry_l O hZF hq.1 (check_name_l M (check_range_l M hZF) hc check) hq.1
      ((name.2 t q).mpr ⟨hq.1,x,a,fn.input_mem_of_pairMember xa,nz,check,xa,qa⟩) (O.refl q hq.1)

theorem Qname_d.value_l {Q T w c L d P τ : M.Domain} (O : Cond_order_d M Q T w)
    {H : M.Domain → Prop} (generic : Generic_d M Q T w H) (name : Qname_d Q c L d P τ)
    {D : (extension_l M hZF Q T w H).Domain} (value : Qval_d M Q T w H τ D)
    (j : M.Domain → (extension_l M hZF Q T w H).Domain)
    (checks : ∀ x t, Check_d M c x t → Qval_d M Q T w H t (j x)) :
    ∀ y, (extension_l M hZF Q T w H).mem y D ↔ ∃ x a,
      M.mem x L ∧ x ≠ d ∧ Entry_d M x a P ∧ (∃ q, H q ∧ M.mem q a) ∧ j x = y := by
  intro y
  apply (qval_mem_l O hZF generic value).trans
  constructor
  · rintro ⟨t,q,tq,hq,ty⟩
    obtain ⟨_,x,a,hx,nz,check,xa,qa⟩ := (name.2 t q).mp tq
    exact ⟨x,a,hx,nz,xa,⟨q,hq,qa⟩,qval_unique_l (checks x t check) ty⟩
  · rintro ⟨x,a,hx,nz,xa,⟨q,hq,qa⟩,rfl⟩
    obtain ⟨t,check⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) c x
    exact ⟨t,q,(name.2 t q).mpr ⟨(generic.proper q hq).1,x,a,hx,nz,check,xa,qa⟩,hq,checks x t check⟩

end YesMetaZFC.Model.Forcing.Internal
