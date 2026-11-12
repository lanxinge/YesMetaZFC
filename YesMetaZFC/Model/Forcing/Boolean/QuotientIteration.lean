import YesMetaZFC.Model.Forcing.Boolean.QuotientGeneric
import YesMetaZFC.Model.Forcing.TwoStep.Names.Isomorphism

/-! # 实际商泛型的二步呈现与双重扩张同构

使用已构造的商名字及旧关系的检查名字。真值定理只局部化首阶段条件，
规范化商关系后，既有名称摊平定理给出组合迭代扩张与双重扩张的满同构。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem quotient_iteration_l {Q T w τ ν : M.Domain} (O : Cond_order_d M Q T w)
    {H : M.Domain → Prop} (small : Generic_d M Q T w H) {c} (hc : H c)
    {D V z : (extension_l M hZF Q T w H).Domain}
    (order : Cond_order_d (extension_l M hZF Q T w H) D V z)
    {G : (extension_l M hZF Q T w H).Domain → Prop}
    (generic : Generic_d (extension_l M hZF Q T w H) D V z G)
    (excluded : ∀ x, (extension_l M hZF Q T w H).mem x D → x ≠ z)
    (value : Qval_d M Q T w H τ D) (relation : Qval_d M Q T w H ν V) :
    ∃ b W C S J, H b ∧ Below_d M Q T w b c ∧ Two_step_d M Q T w b τ ν W C S ∧ Cond_order_d M C S C ∧
      (∀ x y, Entry_d (extension_l M hZF Q T w H) x y J ↔
        (extension_l M hZF Q T w H).mem x D ∧ (extension_l M hZF Q T w H).mem y D ∧
        Entry_d (extension_l M hZF Q T w H) x y V) ∧
      Cond_order_d (extension_l M hZF Q T w H) D J D ∧
      Generic_d (extension_l M hZF Q T w H) D J D G ∧
      Generic_d M C S C (Compose_generic_d M Q T w C H G) ∧
      (∀ q, First_generic_d M Q T (Compose_generic_d M Q T w C H G) q ↔ H q) ∧
      ∃ f : (extension_l M hZF C S C (Compose_generic_d M Q T w C H G)).Domain →
          (extension_l (extension_l M hZF Q T w H) (preserves_zf_l O hZF small) D J D G).Domain,
        (∀ a t, Qval_d M C S C (Compose_generic_d M Q T w C H G) t a →
          Curry_val_d M hZF Q T w C H D J G t (f a)) ∧
        (∀ a b, a ∈ b ↔ f a ∈ f b) ∧ Function.Injective f ∧ Function.Surjective f := by
  let E := extension_l M hZF Q T w H
  have hE := preserves_zf_l O hZF small
  have proper {x} (hx : E.mem x D) : x ≠ D := fun eq => KP.mem_irrefl_d (ZF.modelsKP hE) D (eq ▸ hx)
  have generic' : Generic_d E D V D G := {
    proper := fun x hx => ⟨(generic.proper x hx).1,proper (generic.proper x hx).1⟩
    inhabited := generic.inhabited
    upward := generic.upward
    directed := generic.directed
    meets := fun x hx F dense => generic.meets x hx F (fun y hy => by
      obtain ⟨s,hs,hF⟩ := dense y ⟨hy.1,proper hy.1,hy.2.2⟩
      exact ⟨s,⟨hs.1,excluded s hs.1,hs.2.2⟩,hF⟩) }
  have preord : Preord_d E D V := ⟨order.refl,order.trans⟩
  obtain ⟨J,graph,OJ,transfer,_⟩ := preord_order_l hE preord
  have hJ := (transfer G).mp generic'
  let φ : Formula 1 2 := preord_m (.bound 0) (.bound 1)
  have closed : φ.FreeClosed := preord_m_freeClosed _ _ rfl rfl
  have values : Env_val_d hZF (ord_env_l M τ ν) (ord_env_l E D V) := by
    intro t
    cases t with
    | free _ => exact relation
    | bound i => exact Fin.cases value (fun _ => relation) i
  obtain ⟨b₀,hb₀,force₀⟩ := (forcing_truth_l O hZF small φ closed _ _ values).mpr
    ((preord_sat_l hE.1 (ord_env_l E D V) (.bound 0) (.bound 1)).mpr preord)
  obtain ⟨b,hb,bb₀,bc⟩ := small.directed b₀ c hb₀ hc
  have pos := small.proper b hb
  have force := (forces_regular_l O hZF φ (ord_env_l M τ ν) (fun t => qval_name_l (values t))).1
    b₀ b (small.proper b₀ hb₀).1 ⟨pos.1,pos.2,bb₀⟩ force₀
  obtain ⟨W,C,S,_,step,OC⟩ := two_step_l O hZF (qval_name_l value) (qval_name_l relation) (small.proper b hb).1 force
  have compose := two_step_compose_l O hZF small step OC hb value relation generic'
  have congruence : ∀ x y, E.mem x D → E.mem y D → (Entry_d E x y V ↔ Entry_d E x y J) :=
    fun x y hx hy => ⟨fun xy => (graph x y).mpr ⟨hx,hy,xy⟩,fun xy => ((graph x y).mp xy).2.2⟩
  exact ⟨b,W,C,S,J,hb,⟨pos.1,pos.2,bc⟩,step,OC,graph,OJ,hJ,compose.1,compose.2.1,
    two_step_iso_l O hZF small step OC value relation congruence OJ hJ hb⟩

end YesMetaZFC.Model.Forcing.Internal
