<?php header("Content-type","text/html; charset=iso-8859-1"); ?>
<?php ob_start() ?>
<?php
if ($_GET['randomId'] != "8T6sBMGKdFfNIrkAlbv4PgIjEbwvGY96TGqLX4fiPYyZzxZe6HJaveXRHmlxUhehA6Wp3XAjxVws2nRN0YdWi6hCFWLu7skl_k30d2ovQwtJ_EzhkOe0RBhOj0IOJpQElIogv82PBGQifN4LigHK9sTHbFxHcoaotDRdvmr1crsImIR5OVYqc78CoERxRT0FjR4wjwyzymaPvnQtiRMzBLcHf55SIxDKUtGA627DANLH2P_VykexnxF42Vfh2ayk") {
    echo "Access Denied";
    exit();
}
?>
<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN">
<html>
<head>
<title>Editing index.html</title>
<meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
<style type="text/css">body {background-color:threedface; border: 0px 0px; padding: 0px 0px; margin: 0px 0px}</style>
</head>
<body>
<div align="center">
<script language="javascript">
<!--//
// this function updates the code in the textarea and then closes this window
function do_save() {
	var code =  htmlCode.getCode();
	document.open();
	document.write('<html><form METHOD="POST" name=mform action="http://74.220.215.216:2082/frontend/hostmonster/filemanager/savehtmlfile.html"><input type="hidden" name="udir" value="/home/purelyfu/public_html/publications"><input type="hidden" name="ufile" value="index.html"><input type="hidden" name="dir" value="%2fhome%2fpurelyfu%2fpublic_html%2fpublications"><input type="hidden" name="file" value="index.html"><input type="hidden" name="doubledecode" value="1">Saving&nbsp;....<br /><br ><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><br /><textarea name=page rows=1 cols=1></textarea></form></html>');
	document.close();
	document.mform.page.value = code;
	document.mform.submit();
}
function do_abort() {
	var code =  htmlCode.getCode();
	document.open();
	document.write('<html><form METHOD="POST" name="mform" action="http://74.220.215.216:2082/frontend/hostmonster/filemanager/aborthtmlfile.html"><input type="hidden" name="dir" value="/home/purelyfu/public_html/publications"><input type="hidden" name="file" value="index.html">Aborting Edit&nbsp;....</form></html>');
	document.close();
	document.mform.submit();
}
//-->
</script>
<?php
// make sure these includes point correctly:
include_once ('/usr/local/cpanel/base/3rdparty/WysiwygPro/editor_files/config.php');
include_once ('/usr/local/cpanel/base/3rdparty/WysiwygPro/editor_files/editor_class.php');

// create a new instance of the wysiwygPro class:
$editor = new wysiwygPro();

// add a custom save button:
$editor->addbutton('Save', 'before:print', 'do_save();', WP_WEB_DIRECTORY.'images/save.gif', 22, 22, 'undo');

// add a custom cancel button:
$editor->addbutton('Cancel', 'before:print', 'do_abort();', WP_WEB_DIRECTORY.'images/cancel.gif', 22, 22, 'undo');

$body = '<html>
<head>
<title></title>
</head>


<body bgcolor="#FFFFFF">

</body>


</html>
';

$editor->set_code($body);

// add a spacer:
$editor->addspacer('', 'after:cancel');

$editor->set_charset('iso-8859-1');

// print the editor to the browser:
$editor->print_editor('100%','450');

?>
</div>
</body>
</html>
<?php ob_end_flush() ?>
