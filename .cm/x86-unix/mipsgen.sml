110.76  x86    
         �   �       -      l�  �B+W3��zB�X j�5�  	 
 G�#�=�g�)��2�δ\  O�履Bu�}?�uOHH U V u njV����#i�*�t  ����}�%C�T�8�   ʤ��|�y4!e��z��  �{Xˀx��5Aٮ�  ��r�!�<N_9L%�_  ����	2m�6�`�p�  UD�G`�έF��:]$�UD�G`�έF��:]$�               n               nB+W3��zB�X j�5�G�#�=�g�)��2�δ\O�履Bu�}?�uOHnjV����#i�*�t��wD�o-z��������}�%C�T�8�ʤ��|�y4!e��z���M����֧R����l�{Xˀx��5Aٮ���r�!�<N_9L%�_����	2m�6�`�p�guid-(sources.cm):mipsgen.sml-1427568840.245
  0    �"   )   -   sw `s0, 0(`s1)
   bge `s0, `s1, `j0
b `j1
   bgt `s0, `s1, `j0
b `j1
   ble `s0, `s1, `j0
b `j1
   blt `s0, `s1, `j0
b `j1
   beq `s0, `s1, `j0
b `j1
   bne `s0, `s1, `j0 `j1
   beqz `s0, `j0
b `j1
   bgez `s0, `j0
b `j1
   bgtz `s0, `j0
b `j1
   blez `s0, `j0
b `j1
   bltz `s0, `j0
b `j1
   bnez `s0, `j0
b `j1
   Invlaid stm   
   jal    jr `s0
   b `j0
   :
   move `d0, 0(`s0)
   li `d0,    (`s0)
   lw `d0,    ($ZERO)
   sw `s0,    (`s1)
   To much arguements   lw `d0, 0(`s0)
   and `d0, `s0, `s1
   andi `d0, `s0,    Invalid exp   div `d0, `s0, `s1
   sub `d0, `s0, `s1
   addi `d0, `s0,    mul `d0, `s0, `s1
   or `d0, `s0, `s1
   ori `d0, `s0,    add `d0, `s0, `s1
   addi `d0, `s0   la `d0, 	   )    	   �  i�    �D$H� �D$;|$wR�T$P�ŋ��   �G   �G  �h8�m �o�w�_�O�2�_�o�t$H�T$L�ȋT$P�D$�ph�� �d$H�h  ��F��D$;|$w>�A��   �G   �G  �o�_�0�_�o�t$H�D$L�D$���   ���d$H�=h  ��H����D$;|$w>�A��   �G   �G  �o�_�0�_�o�t$H�D$L�D$��  ���d$H��g  ��������D$;|$wD�A��   �G   �G�  �q�w�o�_�0�_�o�t$H�D$L�D$��h  ���d$H�g  ����������D$;|$wR��Q�  �G   �G   �G  �A�G�o�w�_�*�_�G�l$H�T$L��t$���  �� �d$H�&g  ���0����D$;|$wB�  �G   �G   �G  �o�_�2�_�o�t$H�T$L�D$��(  ���d$H��f  ��������D$;|$w6���  �G   �G   �0�o�t$H�D$L�D$��t  ���d$H�f  ��������D$;|$wR�Q4��   �G   �G�  �q$�w�q,�w�G�o�_��_�o�I0�D$H�T$L�t$���  �� �d$H�f  ���$����D$;|$wA�����   �G   �G  �w�_�*�_�G�l$H�T$L��t$��4  ���d$H��e  ���������D$;|$w/����   �G   �0�o�t$H�D$L�D$��x  ���d$H�}e  �������D$;|$�  �L$P�T$T�l$X�k�u�V�T$\�D$\�P��D$`�B��  ��O�R�W�L$P�O�G  ��O��W�T$T�W�\$X�_ �P�Z�G$�  �D$���  �w(�t$`�N�O,�D$`�p�w0�L$`�A�G4�t$`�N�O8�D$\�0�w<�E �G@�M�OD��WH�L$\�q�wL�E�GP�M�OT��WX�o�o\�w�w`�Gd  �T$`�Wh�G(�Gl�Gp�   �Oh�Ot�s�ot�D$\�P�K�[��x���Hd  ����D$H��P����D$;|$��   �D$L�l$P��   �G   �G  �h�o�G   �G  �h�o�o�o�G �   �l$��d  �o$�G(  �o�o,�w0�_4�O8�W<�G@�p(��_,�W�o$�D$H�t$L�L$P�t$��t  ��H�d$H�c  ;|$w�m ���c  �������D$;|$w ����k�m�D$H�t$L�t$���  �d$H�Lc  �����T����D$;|$��   �ÉT$T�l$X�p�  �V�W�^�_�n�o��W�^�_�n�o�V�W�^ �_ �n(�o$�V,�W(�^0�_,�h�o0�P�W4�X�_8�n4�o<�V8�W@�n$�u �_�P�t$H�l$L�l$T�t$X�t$P�D$��h  ��H�d$H�b  �������D$;|$��)  �L$T�C<��  �K�O�0�w�K(�O�K8�G�  �3�w�s�w�1�w�s �w �p�w$�G(�  �s�w,�s�w0�o4�w,�G8  �k�o<�k�o@�k�oD�h�oH�k$�oL�i�oP�@�GT�o�oX�G�G\�w`�Gd  �n�oh�q�wl�C,�Gp�K0�Ot��x�G��OĉL$X�K4�؋t$T�l$���h  �l$T�D$X�\$l�ً�;|$��(  �L$T�T$l�  �O�W�_�o�G  �G�G�G�� �G��މD$\�T$��i  ����4��,1��[�T$��,i  ����4��,1��C�D$T�S�k�s�:�f
  �z��	  �D$\���  �o�w�J$�Y�_���O�L$X�l$\�]�\$`�j�u�t$\�t$��h6  �\$X�l$T�T$l�L$��Ti  �U �������E�L$��pi  ����L� �T ��h�@�8u[�  �w�_�T$\�W�\$`�_�G  �o�O�O�L$l�Q�*�_�H�l$H�T$L�T$l�   �t$���'  �� �d$H�} u[�  �w�_�t$\�w�L$`�O�G  �G�G�G�T$l�R�2�_�M�t$H�T$L�T$l�   �D$��8(  �� �d$H�  �w�_�T$\�W�\$`�_�G  �G�O�O�\$l�S�2�_�t$H�T$L�͋T$l�   �D$���(  �� �d$H�l$l�M��D$l�@�h�m|�T$H�L$L�L$\�T$`�d$H�  �w�_�l$\�o�t$`�w�G  �H�O�W�W�L$l�i�u �_�H�t$H�l$L�T$l�   �D$��8'  �� �d$H�T$l�J��l$l�E�h�m|�T$H�L$L�L$\�T$`�d$H�H�P�:u\�  �w�_�D$\�G�\$`�_�G  �O�_�_�t$l�n�u �_�J�t$H�l$L�T$l�   �D$��&  �� �d$H�  �w�_�l$\�o�t$`�w�G  �W�W�W�D$l�h�u �_�t$H�l$L�T$l�   �D$���&  �� �d$H�  �w�_�L$\�O�T$`�W�G  �H�O�W�W�T$l�j�u �_�H�t$H�l$L�T$l�   �D$���%  �� �d$H�H�P�:u\�  �w�_�\$\�_�l$`�o�G  �O�_�_�\$l�k�u �_�J�t$H�l$L�T$l�   �D$��$  �� �d$H�9u\�  �w�_�t$\�w�D$`�G�G  �W�W�W�l$l�m�u �_�I�t$H�l$L�T$l�   �D$���$  �� �d$H�  �w�_�\$\�_�l$`�o�G  �W�W�W�t$l�n�u �_�t$H�l$L�T$l�   �D$��%  �� �d$H�P�H�9u\�  �w�_�t$\�w�D$`�G�G  �W�W�W�D$l�h�u �_�I�t$H�l$L�T$l�   �D$���"  �� �d$H�:u\�  �w�_�\$\�_�l$`�o�G  �O�O�O�L$l�i�u �_�J�t$H�l$L�T$l�   �D$�� #  �� �d$H�  �w�_�t$\�w�D$`�G�G  �O�O�O�\$l�k�u �_�t$H�l$L�ʋT$l�   �D$���#  �� �d$H�l$l�M��D$l�@�h�m|�T$H�L$L�L$\�T$`�d$H�L$l�I��T$l�j�U�j|�D$H�L$L�L$\�T$`�d$H�m�U �:t*�l$l�M��D$l�@�h�m|�T$H�L$L�L$\�T$`�d$H�  �D$���]  �O�L$l�I�O�G  �w�_�L$\�O�\$`�_�G   �]�_$�o�o(�\$l�s��_$�o�J�D$H�t$L�T$l�t$��T^  ��0�d$H��  �D$l�@$�H�O�w�_�t$\�w�D$`�G�L$l�q��_�L$l�Q�M�D$H�t$L�   �t$���!  ���d$H�T$l�B��l$l�m�U�j|�L$H�D$L�L$\�T$`�d$H�M�����  �i�E ��	��   �U�:u_�  �w�_�L$\�O�\$`�_�G  �M�O�_�_�t$l�n�u �_�J�t$H�l$L�T$l�   �D$���e  �� �d$H�T$l�  �w�_�l$\�o�t$`�w�j�u �_�t$H�l$L�   �D$���(  ���d$H����   �U�m�:u\�  �w�_�D$\�G�L$`�O�G  �o�O�O�D$l�h�u �_�J�t$H�l$L�T$l�   �D$���   �� �d$H�} u[�  �w�_�\$\�_�t$`�w�G  �W�O�O�t$l�V�2�_�M�t$H�T$L�T$l�   �D$��p!  �� �d$H�T$l������T$l�������u\��  �D$l�P$�j�o�w�_�D$\�G�T$`�W�T$l�j�u �_�D$l�P�I�t$H�l$L�   �t$���!  ���d$H�T$l�r����m��  �L$l�A$�H�O�w�_�\$\�_�t$`�w�t$l�V�G  �] �_�2�w �B�G$�O�O(�D$l�p��_�L$l�Q�M�D$H�t$L�   �t$��Pg  ��0�d$H�m�L$\�T$`��D$\�@�\$\��L$`�H�L$d�X�\$h�H�L$\��\$X�  �o�w�l$X�o�t$\�w�D$h�G�L$d�O�� �_�\$X�T$\�T$`�D$��$.  ������D$\�@�\$\��L$`�H�L$d�X�\$h�H�L$\��\$X뉋k�l$T�k�K�[�} ��   �}uI�t$\���  �O�_�J$�Y�_���G�D$X�\$\�K�L$`�j�m�l$\�t$��07  �Q����t$\�V�t$\��D$`�r�t$d�B�D$h�r�t$\��D$X�  �O�_�L$X�O�T$\�W�\$h�_�t$d�w�� �G�D$X�l$\�T$`�D$��t/  ������T$\�R�D$\�0�t$`�r�t$d�B�D$h�r�t$\��D$X뉋K�L$T�C�k�s�8��   �xuI�T$\���  �o�w�J$�Y�_���_�\$X�t$\�n�l$`�j�E�D$\�t$���7  �F����L$\�Y�L$\��T$`�K�L$d�S�T$h�K�L$\��T$X�  �o�w�\$X�_�l$\�o�t$h�w�L$d�O�� �W�T$X�D$\�T$`�D$�� /  ������\$\�[�T$\�
�L$`�K�L$d�S�T$h�K�L$\��T$X뉋k�l$T�s�k�[�>��   �~uI�t$\���  �o�_�J$�Y�_���G�D$X�\$\�K�L$`�j�m�l$\�t$���8  �;����D$\�@�T$\�
�L$`�H�L$d�P�T$h�H�L$\��T$X�  �o�_�\$X�_�l$\�o�D$h�G�L$d�O�� �W�T$X�t$\�T$`�D$���.  ������D$\�P�D$\��L$`�B�D$d�J�L$h�B�D$\�
�L$X뉋S�T$T�K�k�s�9��   �yuI�\$\���  �o�w�J$�Y�_���o�l$X�D$\�p�t$`�j�M�L$\�t$���9  �0����T$\�R�D$\��\$`�Z�\$d�B�D$h�Z�\$\��D$X�  �o�w�T$X�W�\$\�_�l$h�o�t$d�w�� �G�D$X�L$\�T$`�D$��x.  �����T$\�R�D$\��\$`�Z�\$d�B�D$h�Z�\$\��D$X뉋k�l$T�k�K�[�} ��   �}uI�t$\���  �O�_�J$�Y�_���G�D$X�\$\�K�L$`�j�m�l$\�t$��P:  �$����t$\�V�t$\��D$`�r�t$d�B�D$h�r�t$\��D$X�  �O�_�L$X�O�T$\�W�\$h�_�t$d�w�� �G�D$X�l$\�T$`�D$���-  �����T$\�R�D$\�0�t$`�r�t$d�B�D$h�r�t$\��D$X뉋L$\�	�Q�T$T�\$\�s�D$T� �Y�S�j8�V�N�^�6�D$H�D$T�D$L�d$H�L$\�)�U�T$`�\$\�s�D$`� �U�J�i8�V�N�^�6�D$H�D$`�D$L�d$H�L$\�)�U�T$d�\$\�s�D$d� �U�J�i8�V�N�^�6�D$H�D$d�D$L�d$H�L$\�)�U�T$h�\$\�s�D$h� �U�J�i8�V�N�^�6�D$H�D$h�D$L�d$H�k�} ��   �u��;uJ�L$\�)�  �L$��H;  �G�U�W�U��o�K�^�D$H�T$L�T$\�t$���;  ���d$H�T$\�J�\$\��q�t$`�A�D$\�L$X�l$T�\$��0;  ������L$\�A�T$\��X�\$`�p�t$\�D$X�l$T�L$��;  ������[��8��   �  �h�o�G   �G�   �w�w�D$\� �G  �P�J�YH�_�G   �o�o �G$   �G(  �G,   �w�w0�H$�A��G4  �_,�_8�W<�G@�l$�oD�w@�t$�O8��L$\�Y�3�S�K�[�   ��H��T$\��  �k�o�r$�N�O���_�\$X�t$\�n�l$`�Z�K�L$\�D$T�l$���?  �����k�T$\�
��  �q$�F�G�o�t$\�V�W�A�I�0�_�U�T$P�m �Q�	�t$H�D$L�t$���@  ���d$H�C����	�r  �Y�@�D$T�+���  �s���	�?  �V�n�:��   �   +Z�)  �L$\�	�Q�T$`�T$\�Ë\$���M  �l$X�L$`��}M�   +���  �  ��_�A�G�w�\$T�_�I�1�_�t$H�L$L�L$X�D$��T0  ���d$H�I��\$H�L$L�\$T�L$X���d$H�} u3�   +u��  �l$\�m �E�D$`��T$\�Ƌt$���L  �R����l$\�U�D$\�0�t$`�B�r�j�
�L$X�\$\�  �L$X�O�o�w�G���W�T$X�T$`�D$���/  ���������   �N�n�9u#�\$\��r�t$`�A�T$\�\$��XK  ������} u%�D$\�0�V�T$`�E��T$\�L$�� J  �����l$\�M�T$\�2�t$`�A�q�i�	�L$X�\$\�B����T$\�J�T$\�*�l$`�A�q�i�	�L$X�\$\������u-�T$\��j�l$`�C�t$\�^�S�l$\�t$�� I  �����D$\�P�l$\�M �L$`�B�r�j�
�L$X�\$\������t>�T$\�
�Y�\$X�l$\�u�D$X� �Y�S�j8�V�N�^�6�D$H�D$X�D$L�d$H�i�p�����  �^���	��   �K�[�9u:�   +A�|  �L$\�1�V�J��T$H�L$L�͋T$\��t$���G  �d$H�;u<�   +s�=  �T$\��S�B��T$H�D$L�ً͋T$\��t$���F  �d$H�D$\��  �B$�H�O�o���O�L$X�l$\�]�\$`�Z�C�D$\�t$T�l$��F  ��������   �S�[�:u'�L$\�1�v�t$`�B�\$T�T$\�L$���D  �~����;u'�D$\�0�N�L$`�C�T$T�T$\�L$���C  �R����T$\��  �Z$�C�G�o���_�\$X�D$\�h�l$`�J�I�L$\�t$T�\$��0C  �����T$\��  �B$�H�O�o���_�\$X�D$\�h�l$`�Z�K�L$\�t$T�l$���B  ������uJ�T$\���  �B$�H�O�o�\$\�[�_�J���_�F�Q�)�\$T�L$`�t$���A  �o����D$\��  �B$�H�O�o���O�L$X�l$\�]�\$`�Z�C�D$\�t$T�l$��0A  �����S�L$\��2�J�L$l�\$\�   �L$���)  �T$T�������������D$;|$��  ��L$\�  �J$�Y�_�o���_�.�l$T�v�t$`�l$���f  ��������`����D$;|$�a  �ÉL$\�  �J$�Y�_�o���_��L$T�h�l$`�l$��0e  �T�����������D$;|$�  �\$T�r�t$`���L$���d  �%����������D$;|$��  ��L$\�  �J$�Y�_�o���_��D$T�N�L$`�l$���c  ��������������D$;|$��  �\$T�Z�\$`���L$��pc  ������`����D$;|$�a  ���  �o�_���_�V�.�\$T���t$`�t$��db  �_�����������D$;|$�  ���  �o�_���_�V�.�\$T���t$`�t$��Xa  �������������D$;|$��  ��L$\�  �J$�Y�_�o���_�.�l$T�v�t$`�l$��0]  ��������������D$;|$��  �\$T�B�D$`���L$���\  ������P����D$;|$�Q  �ÉL$\�  �J$�Y�_�o���_��L$T�h�l$`�l$���[  �D������� ����D$;|$�  �\$T�r�t$`���L$��p[  �����������D$;|$��  �ÉL$\��  �J$�Y�_�o�j�u�w���_��L$T�h�l$`�D$���Z  �������x����D$;|$�y  �L$T�T$`�l$\�T$`�L$��0#  �������D����D$;|$�E  �ÉL$\�  �J$�Y�_�o���_�0�t$T�@�D$`�l$��Z  �8������������D$;|$��  �\$T���J�L$`�L$��|Y  �	����������D$;|$��  ��L$\�  �J$�Y�_�o���_�.�l$T�v�t$`�l$���X  ��������t����D$;|$�u  �\$T�B�D$`���L$��HX  ������D����D$;|$�E  ��L$\��  �J$�Y�_�o�j�E�G���_��L$T�n�l$`�L$���W  �/�����������D$;|$��
  �L$T�l$\�T$`�L$���$  �������������D$;|$��
  ��L$\��  �J$�Y�_�o�j�E�G���_��D$T�N�L$`�L$���V  �������d����D$;|$�e
  �L$T�l$\�T$`�L$��D%  �w������4����D$;|$�5
  �ÉL$\�  �J$�Y�_�o���_�(�l$T�p�t$`�l$�� V  �(������������D$;|$��	  �   +��
  �J�L$`�\$T�L$���U  �������������D$;|$��	  ��L$\��  �J$�Y�_�o�j�E�G���_�.�l$T�v�t$`�L$���T  �������P����D$;|$�Q	  �L$T�l$\�T$`�L$��X&  �c������ ����D$;|$�!	  �ÉL$\��  �J$�Y�_�o�j�u�w���_��L$T�h�l$`�D$��T  ������������D$;|$��  �L$T�l$\�T$`�L$���&  �������������D$;|$��  ��L$\�  �J$�Y�_�o���_��D$T�N�L$`�l$��lS  ��������H����D$;|$�I  �\$T�Z�\$`���L$���R  �]���������D$;|$�  �ÉL$\�  �J$�Y�_�o���_�(�l$T�p�t$`�l$��8R  �������������D$;|$��  �\$T�B�D$`���L$���Q  ������������D$;|$��  ��L$\��  �J$�Y�_�o�j�E�G���_��L$T�n�l$`�L$���P  �������@����D$;|$�A  �L$T�l$\�T$`�L$��h(  �S����������D$;|$�  �L$T�  �J$�q�w�o���w�t$\�B�@�D$`�L$��LP  ��������������D$;|$��  �  �G   �O�G  �G   �o�G  �o�o�w�w �G$  �G(	   �G�G,��0�w��k�l$X�l$��?  �D$T������D����D$;|$�E  �ÉL$T�T$`�l$\�P�D$X�L$��@)  �J���������D$;|$�  ��������������D$;|$��  �\$X�L$T�ڋ�  �J$�q�w�o���O�L$\�[�\$`�D$��XN  ��������������D$;|$��  �\$T�L$\�ډl$X��\$`�L$��*  �������d����D$;|$�e  �\$X�L$T�ʋ�  �Z$�s�w�o���o�l$\�q�t$`�D$�� M  �P�����������D$;|$�  �\$T�L$\�ʉl$X��L$`�L$���*  ������������D$;|$��  �\$X�L$T���  �J$�Y�_�o���G�D$\�N�L$`�l$���K  ��������������D$;|$��  �\$T�L$\�ډl$X��\$`�L$��(+  �������L����D$;|$�M  �\$X�L$T���  �J$�Y�_�o���_�\$\�n�l$`�l$���J  �8������������D$;|$��  �\$T�L$\�ʉl$X��L$`�L$���+  �������������D$;|$��  �\$T���l$\��p�t$`�J$�A�D$X�\$���I  �����������D$;|$��  �\$T�L$\���  �J$�Y�_�o���O�L$X�^�\$`�l$��XH  �l�������,����D$;|$�-  �\$T�L$\�ڋ�  �J$�q�w�o���o�l$X�s�t$`�D$�� G  �������������D$;|$��  �\$T�L$\�ʋ�  �Z$�s�w�o���G�D$X�I�L$`�D$��pE  ��������������D$;|$��  �\$T�L$\��  �J$�Y�_�o���_�\$X�h�l$`�l$��8D  �p�������0����D$;|$�1  �\$X�L$T�  �J$�Y�_�o���w�t$\�j�E�D$`�t$���5  ��������������D$;|$��  �\$X�L$T�  �J$�Y�_�o���w�t$\�j�E�D$`�t$���4  ���������������D$;|$��  �\$X�L$T�  �J$�Y�_�o���O�L$\�j�]�\$`�t$���3  �u��������4����D$;|$�5  �\$X�L$T�  �J$�Y�_�o���o�l$\�j�u�t$`�t$���2  �!�������������D$;|$��   �\$X�L$T�  �J$�Y�_�o���O�L$\�j�]�\$`�t$��2  ���������������D$;|$��   �\$X�L$T�  �J$�Y�_�o���o�l$\�j�u�t$`�t$��@1  �y��������8����D$;|$w=�\$X�L$T�  �J$�Y�_�o���G�D$\�j�M�L$`�t$���0  �)�����8  �L$T�T$l�D$H�D$L   �T$ �D$�������D$�L$T�T$l�D$H����ΐ�;|$w9��L$T�T$X�l$\���V�*�^�v�L$H�D$L�L$T�T$X�D$\�D$P�d$H�]8  ;|$��   �  �o�G   �G  �A�G�o�o�G  �r�w�G    �G$   �G�G(�G,  �G0   �W�W4��*�G8  �w0�w<�o@�WD�D$�GH�OD�L$�o<�*�3�S�K�[�   ��P���7  ��;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p����6  ���;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p��� 6  ���;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p���$5  ���;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p���H4  ���;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p���l3  ���;|$��   �  �o�G   �G  �A�G�o�o�G  �s�w�G    �G$  ��G(�o�o,�G0�   �w(�w4�G8  �B�G<�G@   �W4�WD�o�oH�GL  �GP   �w<�wT�1��GX  �OP�O\�G`�wd�T$�Wh�od�l$�G\��s�S�K�[�   ��p���2  ���;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i �o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`����1  ;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i$�o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`����0  ;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i(�o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`���50  ;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i,�o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`���m/  ;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i0�o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`���.  ;|$��   ���  �o�G   �G  �S�W�G   �G  �+�o�w�w �G$�   �W�W(�G,  �i4�o0�G4   �w(�w8�O�O<�G@  �GD   �W0�WH�S��GL  �oD�oP�_T�WX�t$�w\�OX�L$�_P��0�P�H�X�   ��`����-  ;|$w�3�[�   ����-  �;|$w�3�[�   ���-  ��D$H�������D$;|$w:�D$L��  �o�w�_�h�u �_�t$H�l$L�   �D$���;  ���d$H�p-  �;|$w�  �o��G�s�o�[�����2-  ���<����D$;|$wP�����   �D$��,<  �o�G  �_�w��p �n�u �_�G�t$H�l$L��D$��<<  ���d$H��,  ���;|$w�m ����,  �������D$;|$w#����k�m �m �D$H�t$L�t$��t<  �d$H�,  �������D$;|$w�2�t$H�T$L�   �D$���<  �d$H�O,  ����X����D$;|$w;����   �t$���<  �o�s�.�E�0�o�t$H�D$L�D$��=  ���d$H��+  ;|$w�m ���,  �������D$;|$w �u �t$H�l$L��   �D$��@=  �d$H�+  ����������D$;|$w3�s�.�U��i�l$P�)�D$H�T$L�   �   �t$���=  �d$H�m+  ��x����D$;|$w8���C��J���I�i@�D$H�T$L�t$P�   �   �t$���=  �d$H� +  �����(����D$;|$w6�s��J��2�A�@<�D$P�t$H�T$L�   �   �t$��$>  �d$H��*  ��������D$;|$�  �͋k�U ��\$P�m�Z$�T$T�D$X   �t$��`?  �ՋD$P�u^�  �w�_�O�W�G�  �H�O�l$T�o�W�W �t$T�N �q��W�)��\$H�t$L�ڋT$X�t$�� O  ��(�d$H�   �搐���,����D$;|$ws��݋�n�E �D$P�m�J$�T$T�D$X   �t$���`  �M�������������D$;|$w/��p-�S�T$T�+�l$P�[�D$X�   �T$�� P  �����)  ΐ��;|$wo���  �O�K�O�G   �o�G  �G   �W�W�S��G   �o�o$�_(�W,�t$�w0�O,�L$�_$��0�P�H�X�   ��8���)  ��;|$��   ���  �o�G   �G�   ��W�G  �iD�o�G   �w�w �O�O$�G(  �G,   �W�W0�S��G4  �o,�o8�_<�W@�t$�wD�O@�L$�_8��0�P�H�X�   ��H���x(  ����������D$;|$w)�1�BL�D$P�t$H�L$L�   �   �t$���@  �d$H�7(  ��;|$we�  �o�C�G�G  �G   �O�O���G  �o�o�W �O$�t$�w(�G$�D$�W��[�3�S�K�[�   ��0����'  ;|$wl����  �IP�O�S�W�o�G  �G   �o�o�+�u �G  �O�O �w$�o(�T$�W,�_(�\$�w �u �0�P�H�X�   ��0���N'  ���X����D$;|$w!�ŋ1�jT�t$H�L$L�D$P�D$���A  �d$H�'  ���� ����D$;|$w)�1�B<�D$P�t$H�L$L�   �   �t$�� B  �d$H��&  ��;|$��   �  �C�G�G   �G  �o�O�O�G   �G   �G   �G$   �W�W(��*�G,  �w$�w0�o4�W8�D$�G<�O8�L$�o0�*�C�0�P�H�X�   ��@���?&  ��;|$wl����  �IP�O�S�W�o�G  �G   �o�o�+�u �G  �O�O �w$�o(�T$�W,�_(�\$�w �u �0�P�H�X�   ��0����%  �;|$wl����  �IP�O�S�W�o�G  �G   �o�o�+�u �G  �O�O �w$�o(�T$�W,�_(�\$�w �u �0�P�H�X�   ��0���N%  ���X����D$;|$w2�l$T�2�n�E �0�m�m\�t$H�D$L�D$T�D$P�t$���C  �d$H�%  �������D$;|$w1�\$T�2�^��0�[�[X�\$P�t$H�D$L�\$T�t$��|-  �d$H�$  ��;|$��   ���  �o�G   �G  �O�G   �G  �K�O�W�W �G$   �o�o(�G,  �G0   �w�w4�3��G8  �W0�W<�O@�wD�\$�_H�oD�l$�O<��0�P�H�X�   ��P���$  ����� ����D$;|$w2�l$T�2�n�E �0�m�m\�t$H�D$L�D$T�D$P�t$��(E  �d$H��#  ���غ���D$;|$w1�\$T�2�^��0�[�[X�\$P�t$H�D$L�\$T�t$��(-  �d$H�#  ��;|$��   ���  �o�G   �G  �O�G   �G  �K�O�W�W �G$   �o�o(�G,  �G0   �w�w4�3��G8  �W0�W<�O@�wD�\$�_H�oD�l$�O<��0�P�H�X�   ��P����"  ���;|$wl����  �IP�O�S�W�o�G  �G   �o�o�+�u �G  �O�O �w$�o(�T$�W,�_(�\$�w �u �0�P�H�X�   ��0���f"  ���p����D$;|$w2�l$T�2�n�E �0�m�m\�t$H�D$L�D$T�D$P�t$���F  �d$H�"  ���(����D$;|$w1�\$T�2�^��0�[�[X�\$P�t$H�D$L�\$T�t$���,  �d$H��!  ��;|$��   ���  �o�G   �G  �O�G   �G  �K�O�W�W �G$   �o�o(�G,  �G0   �w�w4�3��G8  �W0�W<�O@�wD�\$�_H�oD�l$�O<��0�P�H�X�   ��P���0!  �����8����D$;|$w2�l$T�2�n�E �0�m�m\�t$H�D$L�D$T�D$P�t$��H  �d$H��   �������D$;|$w1�\$T�2�^��0�[�[X�\$P�t$H�D$L�\$T�t$���,  �d$H�   ��;|$��   ���  �o�G   �G  �O�G   �G  �K�O�W�W �G$   �o�o(�G,  �G0   �w�w4�3��G8  �W0�W<�O@�wD�\$�_H�oD�l$�O<��0�P�H�X�   ��P����  ����� ����D$;|$w2�l$T�1�n�E �0�m�md�t$H�D$L�D$T�D$P�t$��HI  �d$H�  ��������D$;|$w1�\$T�1�^��0�[�[`�\$P�t$H�D$L�\$T�t$��@,  �d$H�g  ��;|$��   ���  �o�G   �G  �O�G   �G   �O�O�G   �G$   �W�W(�+�G,  �w$�w0�o4�_8�L$�O<�W8�T$�o0�+�0�P�H�X�   ��@����  ������D$;|$w2�l$T�2�n�E �0�m�md�t$H�D$L�D$T�D$P�t$��hJ  �d$H�  ��������D$;|$w1�\$T�2�^��0�[�[h�\$P�t$H�D$L�\$T�t$��,  �d$H�G  ��;|$��   ���  �o�G   �G  �Q�W�o�o�G  �_�G    �G$   �w�w(�G,  �G0   �W�W4���G8  �o0�o<�_@�WD�t$�wH�OD�L$�_<��0�P�H�X�   ��P���  ����������D$;|$w2�l$T�2�n�E �0�m�md�t$H�D$L�D$T�D$P�t$���K  �d$H�V  ���`����D$;|$w1�\$T�2�^��0�[�[h�\$P�t$H�D$L�\$T�t$��|+  �d$H�  ��;|$��   ���  �o�G   �G  �Q�W�o�o�G  �_�G    �G$   �w�w(�G,  �G0   �W�W4���G8  �o0�o<�_@�WD�t$�wH�OD�L$�_<��0�P�H�X�   ��P���h  �����p����D$;|$w2�l$T�2�n�E �0�m�md�t$H�D$L�D$T�D$P�t$���L  �d$H�  ���(����D$;|$w1�\$T�2�^��0�[�[h�\$P�t$H�D$L�\$T�t$���*  �d$H��  ��;|$��   ���  �o�G   �G  �Q�W�o�o�G  �_�G    �G$   �w�w(�G,  �G0   �W�W4���G8  �o0�o<�_@�WD�t$�wH�OD�L$�_<��0�P�H�X�   ��P���0  �����8����D$;|$w2�l$T�2�n�E �0�m�md�t$H�D$L�D$T�D$P�t$��N  �d$H��  �������D$;|$w1�\$T�2�^��0�[�[h�\$P�t$H�D$L�\$T�t$��d*  �d$H�  ��;|$��   ���  �o�G   �G  �Q�W�o�o�G  �_�G    �G$   �w�w(�G,  �G0   �W�W4���G8  �o0�o<�_@�WD�t$�wH�OD�L$�_<��0�P�H�X�   ��P����  ����� ����D$;|$��   ;�|B�S�J �I�L$T�s�\$T��L$P�B�P�jl�V�N�^�6�D$P�D$H�D$T�D$L�d$H��   �t$���O  �o�s�n �E�0�o�t$H�D$L�D$���O  ���d$H�\  ���;|$w�m ���_  ��T����D$;|$w#����k�m �m �D$H�t$L�t$���O  �d$H�  ������D$;|$w%�s�F �p��D$H�t$L�T$P�t$���)  �d$H��  ��;|$w�  �O�o�3�o�S�K�[�����  ��;|$��   �  �o�G   �G  �A�G�G   �G  �Rp�W�o�o �G$   �w�w(�G,  �G0   �G�G4���G8  �o0�o<�W@�GD�t$�wH�WD�T$�o<�(�3�i�S�K�[��P���  ;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n�Mt�O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���I  ��T����D$;|$w0�l$T�j�E �0�m�mx�t$H�D$L�D$T�D$P�t$���Q  �d$H�  ���������D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$���'  �d$H�  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���  ���� ����D$;|$w0�l$T�j�E �0�m�mx�t$H�D$L�D$T�D$P�t$��(S  �d$H��  �����ج���D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$��h'  �d$H�  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P����  ��;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n���   �O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���"  �;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n���   �O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���b  ���l����D$;|$w3�l$T�j�E �0�m���   �t$H�D$L�D$T�D$P�t$���U  �d$H�  ��$����D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$���%  �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���/  ��;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n���   �O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���n  �;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n���   �O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���  ��������D$;|$w3�l$T�j�E �0�m���   �t$H�D$L�D$T�D$P�t$���X  �d$H�e  ��p����D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$��<$  �d$H�!  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���{  ���������D$;|$w3�l$T�j�E �0�m���   �t$H�D$L�D$T�D$P�t$���Y  �d$H�1  ��<����D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$���#  �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���G  ��;|$��   ������  �o�G   �G  �N�O�W�W�G  �G�G    �G$  �n���   �O(�W�W,�G0   �o�o4�G8  �G<   �O(�O@���GD  �o<�oH�WL�OP�t$�wT�WP�T$�oH�)�3�S�K�[���X���  ��������D$;|$w3�l$T�j�E �0�m���   �t$H�D$L�D$T�D$P�t$���[  �d$H�=  ��H����D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$���"  �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���S  ����\����D$;|$w3�l$T�j�E �0�m���   �t$H�D$L�D$T�D$P�t$���\  �d$H�	  ������D$;|$w/�\$T�Z�3��[�[<�\$P�D$H�t$L�\$T�t$��0"  �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���  ���D$H��(����D$;|$w:�D$L��  �o�w�_�h�u �_�t$H�l$L�   �D$��,^  ���d$H��
  �;|$w�  �o��G�s�o�[�����
  ��������D$;|$wN�����   �D$���^  �o�G  �w�_�v �n�u �_�G�t$H�l$L��D$���^  ���d$H�>
  �;|$w�m ���C
  ��8����D$;|$w����+�m �D$H�t$L�t$���^  �d$H��	  ������D$;|$w�2�t$H�T$L�   �D$��0_  �d$H��	  ����Р���D$;|$w8����   �t$���_  �o�+�E�0�o�t$H�D$L�D$���_  ���d$H�x	  ���;|$w�m ���{	  ��p����D$;|$w �u �t$H�l$L��   �D$���_  �d$H�0	  �����8����D$;|$w'�+�U�2�t$H�T$L�   �   �D$��`  �d$H��  �������D$;|$w0�+�U�2�A�D$P�)�t$H�T$L�   �   �t$��L`  �d$H�  ����������D$;|$w5����J���i�m@�T$H�D$L�t$P�   �   �t$���`  �d$H�_  ����h����D$;|$w3��J���q�v<�t$P�T$H�D$L�   �   �D$���>  �d$H�  ;|$wl���  �_�Q�W�G   �o�G  �G   �_�_�Y�+�G   �w�w$�o(�_,�T$�W0�o,�l$�w$�3�0�)�P�H�X��8���  ��������D$;|$w!�ŋ1�jT�t$H�L$L�D$P�D$���a  �d$H�g  ����p����D$;|$w)�1�B<�D$P�t$H�L$L�   �   �t$���a  �d$H�'  ��;|$��   �  ��G�G   �G  �o�O�O�G   �G   �G   �G$   �W�W(�C�0��G,  �W$�W0�O4�w8�l$�o<�O8�L$�W0��p�+�P�H�X��@���  ��������D$;|$w!�ŋ1�j\�t$H�L$L�D$P�D$���b  �d$H�[  ����d����D$;|$w)�1�B`�D$P�t$H�L$L�   �   �t$���b  �d$H�  ��;|$��   �  ��G�G   �G  �o�O�O�G   �G   �G   �G$   �W�W(�C�0��G,  �W$�W0�O4�w8�l$�o<�O8�L$�W0��p�+�P�H�X��@���  ��������D$;|$w0�l$T�j�E �0�m�m\�t$H�D$L�D$T�D$P�t$���c  �d$H�@  �����H����D$;|$w/�\$T�Z�3��[�[X�\$P�D$H�t$L�\$T�t$�� !  �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���S  ����\����D$;|$w0�l$T�j�E �0�m�m\�t$H�D$L�D$T�D$P�t$���d  �d$H�  ���������D$;|$w/�\$T�Z�3��[�[X�\$P�D$H�t$L�\$T�t$���   �d$H��  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���  ����(����D$;|$w+�   +�p'�r�N�1�t$H�L$L�͋�D$��f  �d$H��  ΐ��������D$;|$w0�l$T�j�E �0�m�m\�t$H�D$L�D$T�D$P�t$��df  �d$H�  ����������D$;|$w/�\$T�Z�3��[�[X�\$P�D$H�t$L�\$T�t$��P   �d$H�M  ;|$��   ������  �o�G   �G  �G�G   �G  �N�O�W�W �G$   �o�o(�G,  �G0   �O�O4���G8  �o0�o<�W@�OD�t$�wH�WD�T$�o<�)�3�S�K�[���P���  ���������D$;|$wO�ÉL$T�T$X�  �o�H�O�L$X�1�_�(�P�H�t$H�t$X�t$L�D$T�D$P�D$���g  ���d$H�A  ��L����D$;|$w$�ŋ1���   �t$H�L$L�D$P�D$���g  �d$H�  ���������D$;|$w)�1�B<�D$P�t$H�L$L�   �   �t$��0h  �d$H��   ��;|$��   �  ��G�G   �G  �o�O�O�G   �G   �G   �G$   �W�W(�C�0��G,  �W$�W0�O4�w8�l$�o<�O8�L$�W0��p�+�P�H�X��@���5;|$w-��L$P�T$T��(�N��^�v�T$H�L$L�L$P�T$T�d$H� �D$H   �D$L   �T$ ���T$ �d$H���������f���l���ı���������X���d���o���z�����������Ϯ�����K����������b���������������������-���W������������������ ���C���m���mipsgen.sml    1p�MipsGen"5DBnB��M����֧R����l" sA A1pB�BsAA4pB��wD�o-z����"A�A cCB�G�#�=�g�)��2�δ\\" aE4h"formals"h"locals"h"name"h"offset"4aAnC"list"1a�nB��0��nC"ref"���Bp"O�履Bu�}?�uOH" aAnC�int"00i1b��0aCBp"��\��}�%C\�T�8�" ��nBp"�{Xˀx��5Aٮ�"00i2b"label"d"Temp"0��%0i2�frame"d"MipsFrame"i2��%�pB�7ABA c��i2b"access"�pB�7AB� b na1��#bB�71c�frag"2da"PROC"B saE2h"body"h��&2aAnBp"njV����#i�*�t"0aG 0da"STRING"BsaE2h"1"h"2"2��3��nC"string"0 fS 1��i3��6�Frame"�pB�7AB�  b na1��>bB�71c�register"1da"Reg"As��  fS 0i3����-�Bi2��-�Bi1�A 2b7�B��C����������C����������C����������N��